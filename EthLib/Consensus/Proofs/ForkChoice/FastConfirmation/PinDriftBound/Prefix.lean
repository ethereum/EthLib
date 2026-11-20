module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumReserve
public import EthLib.Consensus.Proofs.Transition.BalanceDrift
public import EthLib.Consensus.Proofs.Transition.FfgJustification
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.SlashedExit
public import EthLib.Consensus.Proofs.Transition.SlashedPersistence
public import EthLib.Consensus.Proofs.Transition.EpochReads
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
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Assembly
import EthLib.Consensus.Proofs.Transition.BalanceNotRaised
import EthLib.Consensus.Proofs.Transition.InactivityLeakBound
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumDriftBound
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
import EthLib.Consensus.Proofs.Transition.ValidatorCaps
public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Bound
import EthLib.Consensus.Proofs.Transition.Totality.Supply
import EthLib.Consensus.Proofs.Transition.EffectiveFall
import EthLib.Consensus.Proofs.DirectSafety.Evidence
import EthLib.Consensus.Proofs.DirectSafety.Fields
import EthLib.Consensus.Proofs.Transition.ValidatorKeys
import EthLib.Consensus.Proofs.Transition.ChainRoots
import EthLib.Consensus.Proofs.DirectSafety.DepartureQueue
import EthLib.Consensus.Proofs.Transition.ActivationExitOrder
import EthLib.Consensus.Proofs.Transition.SlashedFlags
import EthLib.Consensus.Proofs.Transition.LookaheadActive
import Mathlib.Data.Nat.ModEq
import EthLib.Consensus.Proofs.DirectSafety.IntervalBounds
import EthLib.Consensus.Proofs.Transition.BlockCredits
import EthLib.Consensus.Proofs.DirectSafety.Apriori.BlockFold
public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Ceiling
public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Issuance
public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Ownership
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Branch
import EthLib.Consensus.Proofs.Transition.EpochRewards
import EthLib.Consensus.Proofs.Transition.RewardDeltas
import EthLib.Consensus.Proofs.Transition.FfgStake
import EthLib.Consensus.Proofs.Time
import EthLib.Consensus.Proofs.Participation
import Mathlib.Algebra.Order.Floor.Div

/-!
# The quorum of a call drifts by at most its pin reserve, on another branch

A call of the fast confirmation rule reads the pulled-up head state R of an honest store.

A counting state C of another honest store may lie on another branch since the finalized checkpoint.

The two branches leave one split state, at or after the finalized checkpoint's epoch.

The pin reserve bounds quorum drift from R to C for `fusaka ≤ fork < glamsterdam`.

## Keys active only in the previous epoch of the counting state

A key that counts in C's quorum but is not active at C's epoch exits by the epoch after R's.

When activity up to C's epoch is fixed at the split, R reads that exit exactly.

So `pinReserve` charges such a key in its `exiting` term.

A slashed key there was slashed after the split, since C does not hold the slashing.

A slashing sets the withdrawable epoch at least `EPOCHS_PER_SLASHINGS_VECTOR` after it.

## The penalties of one key over several epochs

A key pays penalties only in the rewards pass at the end of each epoch.

The pass reads the total, the key's effective balance and its score at the epoch's last state.

So a bound on that rate at each such state bounds the key's penalties over the branch.

## The band of totals

The reserve bounds the rates on both branches using the call's total active balance.

The a priori guard at the finalized state supplies a floor and a ceiling on each total.

Before Gloas, twice the last ceiling of the window is at most three times its last floor.

So two totals of the window are within three halves of each other.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-- The key of a step's slashing evidence is the key of a validator of the step's first state. -/
private theorem slashingEvidence_key {x y : ForkedBeaconState preset} (st : Step config checks x y)
    {key : Cryptography.Bls.BLSPubkey} (evidence : st.SlashingEvidence key) :
    ∃ (j : ℕ) (v : Validator), x.state.validators.data[j]? = some v ∧ v.pubkey = key := by
  cases st with
  | slot _ => exact False.elim evidence
  | block engine signed due ok =>
    rcases evidence with ⟨_, _, v, found, key⟩ | ⟨_, _, i, _, v, found, key⟩
    · exact ⟨_, v, found, key⟩
    · exact ⟨_, v, found, key⟩

/-- A validator that first appears in a step, at a position the first state lacks, is unslashed.

A slashed validator of the last state has a slashed key at the first state.

Otherwise the step carries a slashing that names its key.

Either way a validator of the first state holds that key.

The keys of a run from genesis are distinct. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.fresh_unslashed {g m n :
  ForkedBeaconState preset}
    (toM : Run config checks g m) (step : Step config checks m n)
    (genesis : Genesis config checks g) {i : ℕ} (fresh : m.state.validators.data.size ≤ i)
    {w : Validator} (found : n.state.validators.data[i]? = some w) : w.slashed = false := by
  by_contra not
  have slashed : w.slashed = true := by simpa using not
  have unique : PubkeysDistinct n.state := (toM.snoc step).pubkeysDistinct genesis
  have kept := (validatorKeys_prefix_and_distinct_of_chainSteps
    (Relation.ReflTransGen.single step.chainStep)).1
  have taken : ∀ (j : ℕ) (v : Validator), m.state.validators.data[j]? = some v →
      v.pubkey = w.pubkey → False := by
    intro j v read key
    obtain ⟨current, currentRead, currentKey⟩ :=
      validators_getElem?_of_validatorKeys_prefix kept read
    have same := unique.index_eq currentRead found (currentKey.trans key)
    have inside := (Array.getElem?_eq_some_iff.mp read).1
    omega
  have member : w ∈ n.state.validators.data.toList := Array.mem_toList_iff.mpr
    (Array.mem_of_getElem? found)
  rcases (Run.nil.snoc step).slashed_evidence w member slashed with
    ⟨v, memberV, key, -⟩ | ⟨a, b, st, contained, evidence⟩
  · obtain ⟨j, read⟩ := List.mem_iff_getElem?.mp memberV
    exact taken j v (by simpa using read) key
  · cases contained with
    | last =>
      obtain ⟨j, v, read, key⟩ := slashingEvidence_key step evidence
      exact taken j v read key
    | earlier inner _ => cases inner

/-- A key that R slashed and C did not has waited the slashings vector.

The key may be one of the split's registry, or one that joined the registry after the split.

It is slashed on R's branch after the split, or after it joined.

So its withdrawable epoch is at least the split's epoch plus `EPOCHS_PER_SLASHINGS_VECTOR`.

A run keeps every slashing, so the counting state would hold a key slashed at the split slashed. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.slashed_waits {g :
  ForkedBeaconState preset}
    {split pulled counted : BeaconState preset fork}
    (toSplit : Run config checks g ⟨fork, split⟩) (genesis : Genesis config checks g)
    (toPulled : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    (toCounted : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    (early : fork < .glamsterdam) (caps : CapOrder preset)
    (withdrawDelay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {i : ℕ} {validator : Validator} (found : pulled.validators.data[i]? = some validator)
    (slashed : validator.slashed = true)
    (unslashedC : ((counted.validators.data[i]?).map (·.slashed)).getD true = false) :
    (getCurrentEpoch split).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
      validator.withdrawableEpoch.toNat := by
  by_cases inside : i < split.validators.data.size
  · have oldFound := Array.getElem?_eq_getElem inside
    cases oldSlashed : split.validators.data[i].slashed
    · exact (toPulled.newly_slashed_withdrawableEpoch caps.activation caps.compounding early
        withdrawDelay i _ validator oldFound found oldSlashed slashed).2
    · obtain ⟨now, nowFound, nowSlashed⟩ :=
        toCounted.slashedPersistence i _ oldFound oldSlashed
      simp [nowFound, nowSlashed] at unslashedC
  · -- The key joined the registry in R's run, and it was not slashed when it first appeared.
    obtain ⟨m, n, pre, step, post, -, notYet, arrived⟩ := Run.split_at_flip toPulled
      (fun z => i < z.state.validators.data.size) inside
      (Array.getElem?_eq_some_iff.mp found).1
    obtain ⟨w, arrivedFound⟩ : ∃ w, n.state.validators.data[i]? = some w :=
      ⟨_, Array.getElem?_eq_getElem arrived⟩
    have unslashedAtN := PinDrift.Internal.fresh_unslashed (toSplit.append pre) step genesis
      (Nat.le_of_not_lt notYet) arrivedFound
    have delayed := (post.newly_slashed_withdrawableEpoch caps.activation caps.compounding early
      withdrawDelay i w validator arrivedFound found unslashedAtN slashed).2
    have forward : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch n.state).toNat :=
      UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps (pre.snoc step).chainSteps)
    omega

open DirectSafety DirectSafety.Apriori.Internal

/-- The rate at which one rewards pass can debit a key, read at the last state of the epoch.

It reads the total active balance, the key's effective balance and its score there.

The pass reads the score after its update, which adds at most the score bias. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.passPenaltyRate (config : Config) (z :
  ForkedBeaconState preset) (v : ℕ) : ℕ :=
  let total := activeBalanceTotal z.state
  let score := if altair : .altair ≤ z.fork then
      (((z.state.inactivityScores altair).data[v]?).map (·.toNat)).getD 0 else 0
  (TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat) * preset.BASE_REWARD_FACTOR.toNat *
      effectiveAt z v / (WEIGHT_DENOMINATOR.toNat * total.sqrt) +
    effectiveAt z v * (score + config.INACTIVITY_SCORE_BIAS.toNat) /
      (config.INACTIVITY_SCORE_BIAS.toNat *
        (parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat)

/-- The penalties of one key in one segment of a branch fit its pass rate.

This holds if the segment ends an epoch, and the penalties are zero otherwise.

The rate is asked only at the last pass state.

It is asked only when that state reads a total active balance and a base reward per increment.

Every step of the segment starts at the epoch of its start `m`.

Inside the epoch only blocks run, and they record no penalty.

The slot that ends the epoch runs the rewards pass, read at its last state.

So a segment that stays in its epoch pays nothing. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.segment_passDebit_le_guarded {m n :
  ForkedBeaconState preset}
    (mid : Run config checks m n) (early : n.fork < .glamsterdam) (altair : .altair ≤ m.fork)
    (high : ℕ) (endEpoch : (getCurrentEpoch n.state).toNat ≤ high + 1)
    (starts : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      mid.Contains step → getCurrentEpoch u.state = getCurrentEpoch m.state)
    {v : ℕ} (inside : v < m.state.validators.data.size) (pen : ℕ)
    (rate : ∀ {z : ForkedBeaconState preset} (pre : Run config checks m z)
      (ok : advanceSlotAcross config checks z = .ok n), mid = pre.snoc (Step.slot ok) →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch n.state).toNat →
      (∃ total perIncrement, getTotalActiveBalance z.state = .ok total ∧
        getBaseRewardPerIncrement preset total = .ok perIncrement) →
      PinDrift.Internal.passPenaltyRate config z v ≤ pen)
    {found : List (BalanceEvent preset)} (replayed : mid.balanceEvents high = .ok found) :
    (found.map (penaltyDebit v)).sum ≤
      if getCurrentEpoch m.state < getCurrentEpoch n.state then pen else 0 := by
  rcases DirectSafety.Apriori.Internal.segment_events_cases mid early altair high endEpoch starts
      replayed with same | ⟨u, inner, boundary, during, crossings, cached, rfl, uEarly, uEpoch,
      crossing, duringOk, cachedOk, crossingsFree, -, kind⟩
  · -- A segment inside its epoch runs only blocks, which record no penalty.
    have free := (epoch_sync_data mid altair early same high replayed).2.1
    rw [penaltyDebit_sum_zero_of_free free]
    exact Nat.zero_le _
  rw [ite_eq_left (uEpoch ▸ crossing)]
  have free := (epoch_sync_data inner altair uEarly uEpoch high duringOk).2.1
  rcases kind with rfl | ⟨just, pass, rewarded, later, justified, scored, rewardedOk, rfl,
    laterSources, -⟩
  · simp only [List.map_append, List.sum_append, penaltyDebit_sum_zero_of_free free,
      penaltyDebit_sum_zero_of_free crossingsFree]
    exact Nat.zero_le _
  have altairU : .altair ≤ u.fork := Nat.le_trans altair (fork_le_of_chainSteps inner.chainSteps)
  have laterFree : PenaltyFree later := fun e member => by
    rcases laterSources e member with s | s | s <;> simp [s]
  simp only [List.map_append, List.sum_append, penaltyDebit_sum_zero_of_free free,
    penaltyDebit_sum_zero_of_free laterFree, penaltyDebit_sum_zero_of_free crossingsFree,
    Nat.zero_add, Nat.add_zero]
  -- The pass reads the registry, the slot and the scores of `u`, after one update of the scores.
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  have one := justified.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have two := scored.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have validators : pass.validators = u.state.validators := two.1.trans one.1
  have slot : pass.slot = u.state.slot := two.2.2.2.2.trans one.2.2.2.2
  have passEpoch : getCurrentEpoch pass = getCurrentEpoch u.state := by
    simp only [getCurrentEpoch, slot]
  have scoredOk : processInactivityUpdates config just altairU = .ok pass := by
    simpa only [EpochStage.Edge, altairU, ↓reduceDIte] using scored
  have justScores := processJustificationAndFinalization_inactivityScores justified
  have grows := registryGrows_of_chainSteps inner.chainSteps
  have insidePass : v < pass.validators.data.size := by rw [validators]; omega
  rcases replayRewards_penalty_scalar_cases altairU (pass.validators.bound uEarly) rewardedOk {v}
      (fun j member => by rw [Finset.mem_singleton.mp member]; exact insidePass) with
    ⟨total, perIncrement, passTotal, perOk⟩ | quiet
  swap
  · simp only [Finset.sum_singleton] at quiet
    rw [quiet]
    exact Nat.zero_le _
  set score := (if later : .altair ≤ u.fork then
      (((u.state.inactivityScores later).data[v]?).map (·.toNat)).getD 0 else 0) with scoreDef
  have bound := passPenalties_le altairU (pass.validators.bound uEarly) rewardedOk passTotal {v}
    (fun j member => by rw [Finset.mem_singleton.mp member]; exact insidePass)
    (maxScore := score + config.INACTIVITY_SCORE_BIAS.toNat) (fun j member found' updated => by
      rw [Finset.mem_singleton.mp member] at updated
      obtain ⟨old, olds, raised⟩ := processInactivityUpdates_score_le scoredOk updated
      rw [justScores] at olds
      have : old.toNat = score := by simp [scoreDef, altairU, olds]
      omega)
  simp only [Finset.sum_singleton] at bound
  have totalU : getTotalActiveBalance u.state = .ok total := by
    simpa only [getTotalActiveBalance, getActiveValidatorIndicesChecked, getTotalBalance,
      validators, passEpoch] using passTotal
  refine bound.trans (le_trans ?_ (rate inner boundary rfl
    (UInt64.lt_iff_toNat_lt.mp crossing) ⟨total, perIncrement, totalU, perOk⟩))
  -- The pass's reads are those of `u`.
  have weight : eligibleWeight pass v ≤ effectiveAt u v := by
    unfold eligibleWeight
    simp only [validators, effectiveAt]
    split <;> [split <;> simp_all; simp]
  unfold PinDrift.Internal.passPenaltyRate
  dsimp only
  rw [← getTotalActiveBalance_toNat totalU, ← scoreDef]
  apply Nat.add_le_add
  · apply Nat.div_le_div_right
    exact Nat.mul_le_mul_left _ weight
  · apply Nat.div_le_div_right
    exact Nat.mul_le_mul_right _ weight

/-- The penalties of one key over a branch from Altair are at most its pass rate per epoch ended.

The rate must hold at each state of the branch before the epoch of its end.

The branch ends `epoch y - epoch x` epochs, and each runs one rewards pass.

The cut induction of the a priori bound, `run_cuts_le`, sums the segments. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Run.passDebit_le {x y :
  ForkedBeaconState preset} (tail : Run config checks x y)
    (early : y.fork < .glamsterdam) (altair : .altair ≤ x.fork) (high : ℕ)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    {v : ℕ} (inside : v < x.state.validators.data.size) (pen : ℕ)
    (rate : ∀ {z : ForkedBeaconState preset} (pre : Run config checks x z)
      (post : Run config checks z y), tail = pre.append post →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch y.state).toNat →
      (∃ total perIncrement, getTotalActiveBalance z.state = .ok total ∧
        getBaseRewardPerIncrement preset total = .ok perIncrement) →
      PinDrift.Internal.passPenaltyRate config z v ≤ pen)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    (events.map (penaltyDebit v)).sum ≤
      ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) * pen := by
  have total := run_cuts_le high tail early
    (fun z => (∃ total perIncrement, getTotalActiveBalance z.state = .ok total ∧
        getBaseRewardPerIncrement preset total = .ok perIncrement) →
      PinDrift.Internal.passPenaltyRate config z v ≤ pen)
    (penaltyDebit v) (fun t => if t < ix x y then pen else 0) rate
    (fun {m n} toM mid rest starts rates {found} found_ok => by
      have nEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) early
      have ny := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest.chainSteps)
      have segment := PinDrift.Internal.segment_passDebit_le_guarded mid nEarly
        (Nat.le_trans altair (fork_le_of_chainSteps toM.chainSteps)) high (by omega) starts
        (Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps toM.chainSteps)) pen
        (fun {z} preZ ok split before totals =>
          rates preZ (Run.nil.snoc (Step.slot ok)) split before totals)
        found_ok
      refine segment.trans ?_
      split
      · rename_i before
        have := UInt64.lt_iff_toNat_lt.mp before
        have xm := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps toM.chainSteps)
        simp only [ix]
        rw [ite_eq_left (by omega)]
      · exact Nat.zero_le _)
    (ix x y + 1) (fun step member => steps_before_end tail step member) replayed
  -- Each epoch that the branch ends counts `pen`, and the epoch of its end counts nothing.
  rw [List.range_succ, List.map_append, List.sum_append,
    List.map_congr_left (g := fun _ => pen)
      (fun t member => ite_eq_left (List.mem_range.mp member)),
    List.map_const', List.sum_replicate, List.length_range] at total
  simpa [ix] using total

/-- The sync debit of one key in one event. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.syncDebit (v : ℕ) (event : BalanceEvent
  preset) : ℕ :=
  if event.source = .sync then actualBalanceAt event.before v - actualBalanceAt event.after v else 0

/-- The sync credit of a key in one event. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.syncCredit (v : ℕ) (event :
  BalanceEvent preset) : ℕ :=
  if event.source = .sync then actualBalanceAt event.after v - actualBalanceAt event.before v else 0

/-- The balance of a key that stays unslashed falls over a branch only by its debits, as events.

It starts from the smaller of its balance and its largest effective balance.

The debits are the penalties, the sync penalties and the partial withdrawals of its events.

The guards are those of the per-key floor of the a priori bound.

A key with no activation epoch is allowed if the branch starts from Fulu or later. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Run.balanceFloor_events_or_fulu {g
  x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (early : y.fork < .glamsterdam) (high : ℕ)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (v : ValidatorIndex) (val : Validator) (initial : x.state.validators.data[v.toNat]? = some val)
    (unslashed : val.slashed = false)
    (activated : val.activationEpoch ≠ FAR_FUTURE_EPOCH ∨ .fusaka ≤ x.fork)
    (quotient : ℕ) (positive : 0 < quotient)
    (guards : ∀ {m n : ForkedBeaconState preset} (pre : Run config checks x m)
      (step : Step config checks m n) (post : Run config checks n y),
      (pre.snoc step).append post = tail → ∀ w, n.state.validators.data[v.toNat]? = some w →
      (high + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[v.toNat]? = some u → high + 1 < u.withdrawableEpoch.toNat) ∧
      (getCurrentEpoch m.state).toNat < (getCurrentEpoch x.state).toNat +
        preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
          (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat ∧
      quotient ≤ (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
      ∀ events, step.balanceEvents = .ok events → ∀ e ∈ events, e.source ≠ .crossing)
    (stays : ∀ w, y.state.validators.data[v.toNat]? = some w → w.slashed = false)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    min (actualBalanceAt x v.toNat) (withdrawalMaxEffectiveBalance preset x.fork val).toNat ≤
      actualBalanceAt y v.toNat + (events.map (penaltyDebit v.toNat)).sum +
        (events.map (PinDrift.Internal.syncDebit v.toNat)).sum + (events.map (floorPartialDebit
          v)).sum := by
  obtain ⟨last, trace, balance, debt, -, w, final, -, used, -⟩ :=
    FloorTrace.run_of_le_cap_or_fulu shared tail genesis caps delay early high endEpoch v val
      initial
      unslashed
      activated (min (actualBalanceAt x v.toNat)
        (withdrawalMaxEffectiveBalance preset x.fork val).toNat) 0 quotient
      (Nat.min_le_right _ _) positive guards replayed
  have clean : last.slashedHigh = none := by
    cases flag : last.slashedHigh with
    | none => rfl
    | some _ => simp [flag, stays w final] at used
  have floor := FloorTrace.unslashed_balance_floor trace (by simp) clean
  have split : (events.map (floorPenaltyDebit v.toNat)).sum =
      (events.map (penaltyDebit v.toNat)).sum + (events.map (PinDrift.Internal.syncDebit
        v.toNat)).sum := by
    rw [← List.sum_map_add]
    rfl
  rw [balance, debt, split] at floor
  omega

/-- The partial payments to one key are a cost that selects that key's queued entries. -/
private theorem partialCost_key (v : ValidatorIndex) :
    PartialCost (config := config) (checks := checks) (floorPartialDebit (preset := preset) v)
      (fun entry => decide (entry.validatorIndex = v)) where
  quiet e source := by simp [floorPartialDebit, source]
  paid := by
    intro _ _ _ electra _ _ _ _ _ _ computed
    simpa [floorPartialDebit, electra, computed] using
      (getPendingPartialWithdrawals_taken computed).2 v
  slot ok early _ replayed := List.sum_eq_zero fun _ member => by
    obtain ⟨e, present, rfl⟩ := List.mem_map.mp member
    simp [floorPartialDebit, slot_events_no_withdrawals ok early replayed e present]

/-- The partial payments to one key, plus its entries left queued, fit its entries at the start.

The branch is from Electra.

The entries counted are those due by the cutoff.

The cutoff is less than the start epoch plus the minimum withdrawability delay.

This leaves out the extra wait of one epoch plus the seed lookahead before exit churn can start. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Run.partialDebit_net {x y :
  ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (high cutoff : ℕ) (endpoint : (getCurrentEpoch y.state).toNat ≤ cutoff)
    (short : cutoff < (getCurrentEpoch x.state).toNat +
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (v : ValidatorIndex) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events) :
    (events.map (floorPartialDebit v)).sum +
        ((((y.state.pendingPartialWithdrawals
          (Nat.le_trans electra (fork_le_of_chainSteps tail.chainSteps))).data.toList.filter
            fun entry => decide (entry.validatorIndex = v)).filter
              (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff)).map (·.amount.toNat)).sum ≤
      ((((x.state.pendingPartialWithdrawals electra).data.toList.filter
        fun entry => decide (entry.validatorIndex = v)).filter
          (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff)).map (·.amount.toNat)).sum := by
  obtain ⟨added, late, bound⟩ :=
    run_partial_queue_net (partialCost_key v) high cutoff electra tail early replayed endpoint
  have none : ((added.filter fun entry => decide (entry.validatorIndex = v)).filter
      (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro entry member
    have := late entry (List.mem_of_mem_filter member)
    simp only [decide_eq_true_eq]
    omega
  rw [none] at bound
  simpa using bound

/-- The partial payments to one key over a branch from Electra fit its entries due by the cutoff.

These are its entries of the queue at the start.

The cutoff is within the withdrawal delay of the start.

An entry appended along the branch is due no earlier than the delay after the start. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Run.partialDebit_le {x y :
  ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (high cutoff : ℕ) (endpoint : (getCurrentEpoch y.state).toNat ≤ cutoff)
    (short : cutoff < (getCurrentEpoch x.state).toNat +
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (v : ValidatorIndex) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events) :
    (events.map (floorPartialDebit v)).sum ≤
      ((((x.state.pendingPartialWithdrawals electra).data.toList.filter
        fun entry => decide (entry.validatorIndex = v)).filter
          (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff)).map (·.amount.toNat)).sum :=
  Nat.le_of_add_right_le (PinDrift.Internal.Run.partialDebit_net tail electra early high cutoff
    endpoint short v
    replayed)

/-! ## The band of totals from the guard at the finalized state -/

section Band

open DirectSafety.Apriori

/-- From Electra, the ceiling of a window grows with the epoch of the window. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.stakeCeilingAt_mono {x :
  ForkedBeaconState preset} {high : ℕ}
    (electra : .pectra ≤ x.fork) {s t : ℕ} (le : s ≤ t) :
    stakeCeilingAt config x high s ≤ stakeCeilingAt config x high t := by
  have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
  have zero : preElectraEpochs config x high = 0 := by simp [preElectraEpochs, notBefore]
  induction le with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    refine ih.trans ?_
    simp only [stakeCeilingAt, stakeCeiling, zero, Nat.lt_irrefl, false_and, ↓reduceIte]
    omega

/-- The floor of a window falls with the epoch of the window. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.stakeFloorAt_anti {x :
  ForkedBeaconState preset} {high : ℕ} {s t : ℕ}
    (le : s ≤ t) : stakeFloorAt config x high t ≤ stakeFloorAt config x high s := by
  induction le with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    refine Nat.le_trans ?_ ih
    simp only [stakeFloorAt, stakeFloor, stakeFloorPath]
    omega

/-- From Electra, the guard bounds twice the window's last ceiling by three times its last floor.

The window's last index is the epoch after `high`, counted from the guarded state's epoch. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.ratio_of_guard {x :
  ForkedBeaconState preset} {high : ℕ}
    (electra : .pectra ≤ x.fork) (guard : aprioriGuardAt config x high) :
    2 * stakeCeilingAt config x high (high + 1 - (getCurrentEpoch x.state).toNat) ≤
      3 * stakeFloorAt config x high (high + 1 - (getCurrentEpoch x.state).toNat) := by
  have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
  have zero : preElectraEpochs config x high = 0 := by simp [preElectraEpochs, notBefore]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ratioGuard, -⟩ := id guard
  rw [zero] at ratioGuard
  have ratio := ratioGuard (high + 1 - (getCurrentEpoch x.state).toNat) (Nat.zero_le _)
    (by unfold driftHorizon; omega)
  simpa [stakeCeilingAt, stakeFloorAt, zero] using ratio

/-- From Electra and before Gloas, take a state reached from a guarded state within its window.

Its total is between the floor and the ceiling of the window at the state's index. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.total_within_guard {g x z :
  ForkedBeaconState preset} {high : ℕ}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : DirectSafety.Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (electra : .pectra ≤ x.fork) (guard : aprioriGuardAt config x high)
    (run : Run config checks x z) (early : z.fork < .glamsterdam)
    (within : (getCurrentEpoch z.state).toNat ≤ high + 1) {total : Gwei}
    (totalOk : getTotalActiveBalance z.state = .ok total) :
    stakeFloorAt config x high (ix x z) ≤ total.toNat ∧
      total.toNat ≤ stakeCeilingAt config x high (ix x z) := by
  obtain ⟨ceiling, -, floor⟩ := ceilingFloor_electra shared run high
    ⟨genesis, parameters, caps, aligned, early, within, guard⟩ twoSlots electra
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps run.chainSteps) early
  have unit := (ceiling_unit_of_guard shared genesis aligned xEarly electra guard).trans
    (PinDrift.Internal.stakeCeilingAt_mono electra (Nat.zero_le (ix x z)))
  refine ⟨floor total totalOk, ?_⟩
  obtain ⟨-, -, value⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok totalOk)
  rw [value]
  exact max_le unit ceiling

/-- From Electra and before Gloas, take two states reached from a guarded state in its window.

Their totals are within three halves of each other.

Both lie between the window's last floor and ceiling.

The guard asks that twice that ceiling be at most three times that floor.

So the band follows from the guard, and nothing assumes it. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.total_band_of_guard {g x y z :
  ForkedBeaconState preset} {high : ℕ}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : DirectSafety.Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (electra : .pectra ≤ x.fork) (guard : aprioriGuardAt config x high)
    (toY : Run config checks x y) (yEarly : y.fork < .glamsterdam)
    (yWithin : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (toZ : Run config checks x z) (zEarly : z.fork < .glamsterdam)
    (zWithin : (getCurrentEpoch z.state).toNat ≤ high + 1) {yTotal zTotal : Gwei}
    (yOk : getTotalActiveBalance y.state = .ok yTotal)
    (zOk : getTotalActiveBalance z.state = .ok zTotal) :
    2 * zTotal.toNat ≤ 3 * yTotal.toNat := by
  have ratio := PinDrift.Internal.ratio_of_guard electra guard
  obtain ⟨yLow, -⟩ := PinDrift.Internal.total_within_guard shared genesis parameters caps aligned
    twoSlots electra
    guard toY yEarly yWithin yOk
  obtain ⟨-, zHigh⟩ := PinDrift.Internal.total_within_guard shared genesis parameters caps aligned
    twoSlots electra
    guard toZ zEarly zWithin zOk
  -- Both indices are at most the window's last index.
  have yAnti := PinDrift.Internal.stakeFloorAt_anti (config := config) (x := x) (high := high)
    (show ix x y ≤ high + 1 - (getCurrentEpoch x.state).toNat by simp only [ix]; omega)
  have zMono := PinDrift.Internal.stakeCeilingAt_mono (config := config) (x := x) (high := high)
    electra
    (show ix x z ≤ high + 1 - (getCurrentEpoch x.state).toNat by simp only [ix]; omega)
  omega

/-- The preset facts that the pin's drift bound needs.

Each field is a fact about the preset alone, and a deployed preset has it. -/
structure PinPresetFacts (preset : Preset) : Prop where
  /-- (preset fact) An increment is at least 900 times the slashings vector. -/
  rounding : 900 * preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  /-- (preset fact) An increment is at least 14 times the slashing quotient. -/
  slash : 14 * (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat ≤
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  /-- (preset fact) The slashings vector has at least four epochs. -/
  vector : 4 ≤ preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat
  /-- (preset fact) The slashing quotient is at least two. -/
  quotient : 2 ≤ (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat
  /-- (preset fact) The margin leaves room for the climb after a third of the stake is lost.

  It reads the maximum effective balance, the band, and the slashing quotient. -/
  margin : 2400 * (2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
      preset.MAX_EFFECTIVE_BALANCE.toNat /
        (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
      preset.downwardBand - 1) + 2400 * preset.downwardBand +
    2400 * ((preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
      (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat - 1) /
        (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat) ≤
    1591 * (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand)
  /-- (preset fact) Ten upward bands fit in the maximum effective balance. -/
  band : 10 * preset.upwardBand ≤ preset.MAX_EFFECTIVE_BALANCE.toNat
  /-- (preset fact) The upward band is at most the downward band and one increment. -/
  upward : preset.upwardBand ≤ preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  /-- (preset fact) The largest slashing penalty and the downward band fit in an increment. -/
  slashBand : preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
      preset.MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA.toNat + preset.downwardBand ≤
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  /-- (preset fact) At every fork the floor of a new key is at least an increment. -/
  newKey : ∀ fork : Fork, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
    2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
      preset.MAX_EFFECTIVE_BALANCE.toNat /
        (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
      preset.downwardBand - preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  /-- (preset fact) At every fork the whistleblower quotient is at least thirty. -/
  whistleblower : ∀ fork : Fork,
    30 ≤ (EthLib.Consensus.parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  /-- (preset fact) The increment times the base reward factor is `2 ^ 35` or more, never small. -/
  rewardScale : 2 ^ 35 ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat
  /-- (preset fact) An increment is at least `10 ^ 8` gwei, which rules out a small increment. -/
  incrementSize : 10 ^ 8 ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  /-- (preset fact) A sync committee period has at least one epoch. -/
  syncPeriod : preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD ≠ 0
  /-- (preset fact) Four downward bands fit in an increment. -/
  quarterBand : 4 * preset.downwardBand ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  /-- (preset fact) The proposer lookahead ends before activity stops being fixed. -/
  covers : preset.MIN_SEED_LOOKAHEAD.toNat + 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat
  /-- (preset fact) The increment times the base reward factor does not overflow a `Gwei`. -/
  fits : preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64
  /-- (preset fact) An increment is at most four downward bands, which rules out a tiny band. -/
  bandLow : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ 4 * preset.downwardBand
  /-- (preset fact) The activation balance is at most the largest effective balance before Electra.

  With the cap order, the two are equal, as the upgrade to Electra needs. -/
  activation : ActivationWithinMaxEffective preset

/-- The downward band is below an increment.

Four bands fit in an increment, and an increment is positive. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.PinPresetFacts.below (facts :
  PinPresetFacts preset) :
    preset.downwardBand < preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  have := facts.quarterBand
  have := facts.incrementSize
  omega

/-- The base reward factor is positive, since its product with an increment is at least `2 ^ 35`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.PinPresetFacts.reward (facts :
  PinPresetFacts preset) :
    1 ≤ preset.BASE_REWARD_FACTOR.toNat := by
  have scale := facts.rewardScale
  rcases Nat.eq_zero_or_pos preset.BASE_REWARD_FACTOR.toNat with zero | positive
  · rw [zero, Nat.mul_zero] at scale
    exact absurd scale (by decide)
  · exact positive

/-- Forty-four slashings vectors fit in three increments.

It compares epochs with gwei, since the unit gain adds two gwei of rounding for each epoch.

An increment is at least 900 slashings vectors. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.PinPresetFacts.vectorSmall (facts :
  PinPresetFacts preset) :
    44 * preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  have := facts.rounding
  omega

/-- The mainnet preset has the preset facts of the pin. -/
theorem PinPresetFacts.mainnet : PinPresetFacts Preset.mainnet :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    fun fork => by cases fork <;> decide, fun fork => by cases fork <;> decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide,
    ActivationWithinMaxEffective.mainnet⟩

/-- The minimal preset has the preset facts of the pin. -/
theorem PinPresetFacts.minimal : PinPresetFacts Preset.minimal :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    fun fork => by cases fork <;> decide, fun fork => by cases fork <;> decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide,
    ActivationWithinMaxEffective.minimal⟩

/-- From Electra and before Gloas, the floor of the window at its start leaves room for the window.

The guard asks that twice the last ceiling be at most three times the last floor.

The ceiling is at least an increment, and the floor falls with the epoch of the window.

So the first floor is at least two thirds of an increment.

The window is shorter than the slashings vector, and an increment is at least 900 vectors.

An increment is also at least 14 slashing quotients, so the first floor is at least 9 quotients. -/
private theorem first_floor_of_guard {g x : ForkedBeaconState preset} {high : ℕ}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (aligned : MaxEffectiveBalancesAligned preset)
    (xEarly : x.fork < .glamsterdam)
    (electra : .pectra ≤ x.fork) (guard : aprioriGuardAt config x high)
    (facts : PinPresetFacts preset) :
    600 * (high + 2 - (getCurrentEpoch x.state).toNat) ≤ stakeFloorAt config x high 0 ∧
      9 * (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat ≤
        stakeFloorAt config x high 0 := by
  have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
  have zero : preElectraEpochs config x high = 0 := by simp [preElectraEpochs, notBefore]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, window, -⟩ := id guard
  have ratio := PinDrift.Internal.ratio_of_guard electra guard
  have unit := (ceiling_unit_of_guard shared genesis aligned xEarly electra guard).trans
    (PinDrift.Internal.stakeCeilingAt_mono electra (Nat.zero_le (high + 1 - (getCurrentEpoch
      x.state).toNat)))
  have anti := PinDrift.Internal.stakeFloorAt_anti (config := config) (x := x) (high := high)
    (Nat.zero_le (high + 1 - (getCurrentEpoch x.state).toNat))
  have rounding := facts.rounding
  have slash := facts.slash
  simp only [stakeCeilingAt, stakeFloorAt, zero] at unit anti ratio ⊢
  unfold driftHorizon at window
  constructor <;> omega

end Band


/-! ## Credits to exiting keys -/

/-- A pending deposit leaves a balance alone unless its key is first found at that position.

The validators only grow at the end. -/
private theorem applyPendingDeposit_frame {s s' : BeaconState preset fork}
    {deposit : PendingDeposit}
    (altair : .altair ≤ fork)
    (computed : applyPendingDeposit config checks s deposit = .ok s') {i : ℕ}
    (inside : i < s.validators.data.size)
    (other : s.validators.data.findIdx? (·.pubkey == deposit.pubkey) ≠ some i) :
    s'.balances.data[i]? = s.balances.data[i]? ∧
      ∃ suffix : List Validator,
        s'.validators.data.toList = s.validators.data.toList ++ suffix := by
  cases hf : s.validators.data.findIdx? (·.pubkey == deposit.pubkey) with
  | some j =>
    have ne : i ≠ j := fun same => other (same ▸ hf)
    exact ⟨(applyPendingDeposit_known_balances hf computed).2 i ne, [], by
      rw [(applyPendingDeposit_known hf computed).2, List.append_nil]⟩
  | none =>
    refine ⟨DirectSafety.Apriori.Internal.applyPendingDeposit_absent_balances altair hf computed
      inside, ?_⟩
    rcases applyPendingDeposit_cases computed with rfl | ⟨_, raised⟩ | ⟨_, added⟩
    · exact ⟨[], by simp⟩
    · exact ⟨[], by rw [increaseBalance_validators raised, List.append_nil]⟩
    · exact ⟨[getValidatorFromDeposit preset fork deposit.pubkey deposit.withdrawalCredentials
        deposit.amount], by rw [addValidatorToRegistry_validators_eq_push added, Array.toList_push]⟩

/-- From Electra, the pending deposits of an epoch leave a key's balance alone.

This holds while the key exits and is not yet withdrawable.

Such a key's deposits are postponed (`processPendingDeposits_postponed_epochs`). -/
private theorem processPendingDeposits_exited_balance {state after : BeaconState preset fork}
    {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after)
    {i : ℕ} {v : Validator} (found : state.validators.data[i]? = some v)
    (exited : v.exitEpoch.toNat < 2 ^ 64 - 1)
    (held : (getCurrentEpoch state).toNat < v.withdrawableEpoch.toNat) :
    after.balances.data[i]? = state.balances.data[i]? := by
  obtain ⟨read, rest, next, pending, carried, -, -, -, folded, rfl⟩ :=
    processPendingDeposits_postponed_epochs computed
  have inside : i < state.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
  have vAt : state.validators.data[i] = v := (Array.getElem?_eq_some_iff.mp found).2
  let P : BeaconState preset fork → Prop := fun s =>
    s.balances.data[i]? = state.balances.data[i]? ∧
      ∃ suffix : List Validator, s.validators.data.toList = state.validators.data.toList ++ suffix
  have final : P next := by
    refine foldlM_ok_invariant_of_mem P (fun s d s' member ⟨bal, suffix, pre⟩ step => ?_)
      ⟨rfl, [], by simp⟩ folded
    have sizeV : state.validators.data.size ≤ s.validators.data.size := by
      have := congrArg List.length pre
      simp only [Array.length_toList, List.length_append] at this
      omega
    have get : ∀ j (hj : j < state.validators.data.size) (hs : j < s.validators.data.size),
        s.validators.data[j] = state.validators.data[j] := by
      intro j hj hs
      have := congrArg (·[j]?) pre
      rw [List.getElem?_append_left (by rw [Array.length_toList]; exact hj),
        Array.getElem?_toList, Array.getElem?_toList, Array.getElem?_eq_getElem hs,
        Array.getElem?_eq_getElem hj] at this
      exact Option.some.inj this
    -- The deposit does not go to position `i`: its key would find `v`, which is postponed.
    have other : s.validators.data.findIdx? (·.pubkey == d.pubkey) ≠ some i := by
      intro hit
      obtain ⟨h, hitMatch, before⟩ := Array.findIdx?_eq_some_iff_getElem.mp hit
      have atI : s.validators.data[i] = v := (get i inside h).trans vAt
      have firstMatch : state.validators.data.find? (·.pubkey == d.pubkey) = some v := by
        rw [← Array.find?_toList, List.find?_eq_some_iff_getElem]
        refine ⟨atI ▸ hitMatch, i, by rw [Array.length_toList]; exact inside,
          by simp [vAt], fun j hj => ?_⟩
        have hjs : j < state.validators.data.size := by omega
        have := before j hj
        rw [get j hjs (by omega)] at this
        simpa using this
      have kept := (List.mem_filter.mp member).2
      rw [firstMatch] at kept
      simp only [Option.any_some, Bool.not_eq_true', Bool.and_eq_false_iff,
        decide_eq_false_iff_not] at kept
      omega
    obtain ⟨bal', suffix', pre2⟩ := applyPendingDeposit_frame
      (Nat.le_trans (show Fork.altair ≤ Fork.pectra by decide) electra) step
      (Nat.lt_of_lt_of_le inside sizeV) other
    exact ⟨bal'.trans bal, suffix ++ suffix', by rw [pre2, pre, List.append_assoc]⟩
  exact final.1

end EthLib.Consensus.Models.Network

namespace EthLib.Consensus.Models.Network

open DirectSafety.Apriori.Internal (recordBalance_single)

section

/-! ## The credits of one key along a run -/

namespace PinKeys

open Base Uint64 Models DirectSafety

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-- The credit of key `i` in one replayed event. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.keyCredit (i : ℕ) (e : BalanceEvent
  preset) : ℕ :=
  actualBalanceAt e.after i - actualBalanceAt e.before i

/-- The credits to the key in one step, from the sources that count at that kind of step. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.stepCredit (blockP slotP :
  BalanceSource → Bool) (v : ℕ)
    {x y : ForkedBeaconState preset} (step : Step config checks x y) : ℕ :=
  let events := step.balanceEvents.toOption.getD []
  match step with
  | .slot _ => ((events.filter (slotP ·.source)).map (PinDrift.Internal.keyCredit v)).sum
  | .block .. => ((events.filter (blockP ·.source)).map (PinDrift.Internal.keyCredit v)).sum

/-- The credits to the key over a run.

The steps count from the one whose start epoch is at most `high + 1`, as in `Run.balanceEvents`. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.creditScan (blockP slotP :
  BalanceSource → Bool) (v high : ℕ)
    {x : ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → ℕ
  | _, .nil => 0
  | _, .snoc (middle := m) pre step =>
    let before := PinDrift.Internal.creditScan blockP slotP v high pre
    if (getCurrentEpoch m.state).toNat ≤ high + 1 then
      before + PinDrift.Internal.stepCredit blockP slotP v step
    else before

/-- The credits that a scan reads from a run, after one more step. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.creditScan_snoc (blockP slotP :
  BalanceSource → Bool) (v high : ℕ)
    {x m y : ForkedBeaconState preset} (pre : Run config checks x m)
    (step : Step config checks m y) :
    PinDrift.Internal.creditScan blockP slotP v high (pre.snoc step) =
      if (getCurrentEpoch m.state).toNat ≤ high + 1 then
        PinDrift.Internal.creditScan blockP slotP v high pre + PinDrift.Internal.stepCredit blockP
          slotP v step
      else PinDrift.Internal.creditScan blockP slotP v high pre := rfl

/-- The credits of a run to a key, read as a scan, add over `append`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.creditScan_append (blockP slotP :
  BalanceSource → Bool) (v high : ℕ)
    {x m y : ForkedBeaconState preset} (pre : Run config checks x m)
    (post : Run config checks m y) :
    (PinDrift.Internal.creditScan blockP slotP v high (pre.append post)) =
      (PinDrift.Internal.creditScan blockP slotP v high pre) + (PinDrift.Internal.creditScan blockP
        slotP v high post) := by
  induction post with
  | nil => rfl
  | snoc post step ih =>
    change (PinDrift.Internal.creditScan blockP slotP v high ((pre.append post).snoc step)) = _
    rw [PinDrift.Internal.creditScan_snoc, PinDrift.Internal.creditScan_snoc]
    split
    · omega
    · exact ih

/-- The credits that a scan reads are 0 if each step of the run credits 0. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.creditScan_eq_zero_of_steps (blockP
  slotP : BalanceSource → Bool) (v high : ℕ)
    {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (zero : ∀ {m n : ForkedBeaconState preset} (step : Step config checks m n),
      tail.Contains step → PinDrift.Internal.stepCredit blockP slotP v step = 0) :
    (PinDrift.Internal.creditScan blockP slotP v high tail) = 0 := by
  induction tail with
  | nil => rfl
  | @snoc m n pre step ih =>
    have prior := ih fun inner member => zero inner (.earlier member step)
    have here := zero step (.last pre step)
    rw [PinDrift.Internal.creditScan_snoc]
    split <;> omega

/-- The credits of a list of events from one source set are at most those from a larger set. -/
private theorem sum_filter_credit_le (p q : BalanceSource → Bool)
    (sub : ∀ s, p s = true → q s = true) (v : ℕ) (L : List (BalanceEvent preset)) :
    ((L.filter (p ·.source)).map (PinDrift.Internal.keyCredit v)).sum ≤
      ((L.filter (q ·.source)).map (PinDrift.Internal.keyCredit v)).sum := by
  induction L with
  | nil => simp
  | cons e rest ih =>
    by_cases inP : p e.source = true
    · have inQ := sub _ inP
      simp only [List.filter_cons, inP, inQ, ↓reduceIte, List.map_cons, List.sum_cons]
      omega
    · by_cases inQ : q e.source = true
      · simp only [List.filter_cons, inP, inQ, Bool.false_eq_true, ↓reduceIte, List.map_cons,
          List.sum_cons]
        omega
      · simp only [List.filter_cons, inP, inQ, Bool.false_eq_true, ↓reduceIte]
        exact ih

/-- The credits of a set of keys over a run, read as a scan, fit one bound for each replayed event.

A block step counts the events of `blockP`.

A slot step counts the events of `slotP`.

So an event of the run is counted at most once.

The credits of a key from a source set `src` over the events are at most its scan.

Each kind of step either counts all of `src`, or records no credit from `src`.

That holds for a run from Electra to before Glamsterdam. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.creditScan_bounds {ι : Type} (S :
  Finset ι) (key : ι → ℕ)
    (blockP slotP : BalanceSource → Bool) (high : ℕ) (T : BalanceEvent preset → ℕ)
    {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (each : ∀ e ∈ events, (blockP e.source = true ∨ slotP e.source = true) →
      ∑ v ∈ S, PinDrift.Internal.keyCredit (key v) e ≤ T e) :
    (∑ v ∈ S, (PinDrift.Internal.creditScan blockP slotP (key v) high tail) ≤
      (events.map fun e =>
        if blockP e.source = true ∨ slotP e.source = true then T e else 0).sum) ∧
    (∀ src : BalanceSource → Bool,
      ((∀ s, src s = true → blockP s = true) ∨
        ∀ {f : Fork} {u w : BeaconState preset f} {engine : ExecutionEngine preset f}
          {signed : SignedBeaconBlock preset f} {due : upgradeDue config ⟨f, u⟩ = false}
          {ok : applySignedBlock config checks engine u signed true = .ok w}
          {es : List (BalanceEvent preset)}, .pectra ≤ f → f < .glamsterdam →
          (Step.block engine signed due ok : Step config checks ⟨f, u⟩ ⟨f, w⟩).balanceEvents =
            .ok es → ∀ i, ((es.filter (src ·.source)).map (PinDrift.Internal.keyCredit i)).sum = 0)
              →
      ((∀ s, src s = true → slotP s = true) ∨
        ∀ {u w : ForkedBeaconState preset} (ok : advanceSlotAcross config checks u = .ok w)
          {es : List (BalanceEvent preset)}, .pectra ≤ u.fork → w.fork < .glamsterdam →
          (Step.slot ok : Step config checks u w).balanceEvents = .ok es →
            ∀ i, ((es.filter (src ·.source)).map (PinDrift.Internal.keyCredit i)).sum = 0) →
      .pectra ≤ x.fork → y.fork < .glamsterdam →
      ∀ v, ((events.filter (src ·.source)).map (PinDrift.Internal.keyCredit v)).sum ≤
        (PinDrift.Internal.creditScan blockP slotP v high tail)) := by
  induction tail generalizing events with
  | nil =>
    simp only [Run.balanceEvents, pure, Except.pure, Except.ok.injEq] at replayed
    subst replayed
    exact ⟨Nat.le_zero.mpr (Finset.sum_eq_zero fun v _ => rfl), fun _ _ _ _ _ v => by simp⟩
  | @snoc middle last pre step ih =>
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    by_cases selected : (getCurrentEpoch middle.state).toNat ≤ high + 1
    · simp only [selected, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
      obtain ⟨added, addedOk, rfl⟩ := rest
      obtain ⟨previous, previousSrc⟩ :=
        ih priorOk fun e member => each e (List.mem_append_left _ member)
      have swap (L : List (BalanceEvent preset)) : ∑ v ∈ S, (L.map (PinDrift.Internal.keyCredit (key
        v))).sum =
          (L.map fun e => ∑ v ∈ S, PinDrift.Internal.keyCredit (key v) e).sum := by
        simpa using (Multiset.sum_map_sum (m := (L : Multiset (BalanceEvent preset)))
          (s := S) (f := fun e v => PinDrift.Internal.keyCredit (key v) e)).symm
      have part (p : BalanceSource → Bool)
          (sub : ∀ s, p s = true → blockP s = true ∨ slotP s = true) :
          ∑ v ∈ S, ((added.filter fun x => p x.source).map (PinDrift.Internal.keyCredit (key
            v))).sum ≤
            (added.map fun e =>
              if blockP e.source = true ∨ slotP e.source = true then T e else 0).sum := by
        rw [swap]
        calc ((added.filter fun x => p x.source).map fun e => ∑ v ∈ S, PinDrift.Internal.keyCredit
          (key v) e).sum
            ≤ ((added.filter fun x => p x.source).map T).sum := List.sum_le_sum fun e member =>
              each e (List.mem_append_right _ (List.mem_filter.mp member).1)
                (sub _ (by simpa using (List.mem_filter.mp member).2))
          _ = (added.map fun e => if p e.source = true then T e else 0).sum := by
              rw [List.sum_map_ite (fun e : BalanceEvent preset => p e.source = true) T
                (fun _ => 0)]
              simp
          _ ≤ _ := List.sum_le_sum fun e _ => by
              by_cases hp : p e.source = true
              · have := sub _ hp
                simp [hp, this]
              · simp [hp]
      have step_le : ∑ v ∈ S, PinDrift.Internal.stepCredit blockP slotP (key v) step ≤
          (added.map fun e =>
            if blockP e.source = true ∨ slotP e.source = true then T e else 0).sum := by
        cases step with
        | slot ok =>
          simp only [PinDrift.Internal.stepCredit, addedOk, Except.toOption, Option.getD_some]
          exact part slotP fun _ h => Or.inr h
        | block engine signed due ok =>
          simp only [PinDrift.Internal.stepCredit, addedOk, Except.toOption, Option.getD_some]
          exact part blockP fun _ h => Or.inl h
      refine ⟨?_, fun src blockKind slotKind electra early v => ?_⟩
      · simp only [PinDrift.Internal.creditScan_snoc, selected, ↓reduceIte, Finset.sum_add_distrib,
          List.map_append, List.sum_append]
        omega
      · have prior := previousSrc src blockKind slotKind electra
          (Nat.lt_of_le_of_lt step.chainStep.fork_le early) v
        have stepSrc : ((added.filter (src ·.source)).map (PinDrift.Internal.keyCredit v)).sum ≤
            PinDrift.Internal.stepCredit blockP slotP v step := by
          have inRun := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
          cases step with
          | slot ok =>
            simp only [PinDrift.Internal.stepCredit, addedOk, Except.toOption, Option.getD_some]
            rcases slotKind with covered | quiet
            · exact sum_filter_credit_le src slotP covered v added
            · rw [quiet ok inRun early addedOk v]
              exact Nat.zero_le _
          | block engine signed due ok =>
            simp only [PinDrift.Internal.stepCredit, addedOk, Except.toOption, Option.getD_some]
            rcases blockKind with covered | quiet
            · exact sum_filter_credit_le src blockP covered v added
            · rw [quiet inRun early addedOk v]
              exact Nat.zero_le _
        simp only [PinDrift.Internal.creditScan_snoc, selected, ↓reduceIte, List.filter_append,
          List.map_append,
          List.sum_append]
        omega
    · simp only [selected, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at rest
      obtain rfl := rest
      obtain ⟨previous, previousSrc⟩ := ih priorOk each
      refine ⟨?_, fun src blockKind slotKind electra early v => ?_⟩
      · simp only [PinDrift.Internal.creditScan_snoc, selected, ↓reduceIte]
        exact previous
      · simp only [PinDrift.Internal.creditScan_snoc, selected, ↓reduceIte]
        exact previousSrc src blockKind slotKind electra
          (Nat.lt_of_le_of_lt step.chainStep.fork_le early) v

/-- The credits of a set of keys over a run, read as a scan, fit one bound for each replayed event.

A block step counts the events of `blockP`.

A slot step counts the events of `slotP`.

So an event of the run is counted at most once. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.creditScan_sum_le {ι : Type} (S :
  Finset ι) (key : ι → ℕ)
    (blockP slotP : BalanceSource → Bool) (high : ℕ) (T : BalanceEvent preset → ℕ)
    {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (each : ∀ e ∈ events, (blockP e.source = true ∨ slotP e.source = true) →
      ∑ v ∈ S, PinDrift.Internal.keyCredit (key v) e ≤ T e) :
    ∑ v ∈ S, (PinDrift.Internal.creditScan blockP slotP (key v) high tail) ≤
      (events.map fun e =>
        if blockP e.source = true ∨ slotP e.source = true then T e else 0).sum :=
  (PinDrift.Internal.creditScan_bounds S key blockP slotP high T tail replayed each).1

/-- The net rise of a key in one step.

A block step counts the rise of the key's balance across it, and a slot step counts nothing. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.stepNet (v : ℕ) {x y :
  ForkedBeaconState preset} (step : Step config checks x y) : ℕ :=
  match step with
  | .block .. => actualBalanceAt y v - actualBalanceAt x v
  | .slot _ => 0

/-- The net credits to the key in the block steps of a run.

A block step counts the rise of the key's balance across the whole step.

A credit that the same step takes back counts for nothing.

The steps count from the one whose start epoch is at most `high + 1`, as in `Run.balanceEvents`. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.netScan (v high : ℕ) {x :
  ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → ℕ
  | _, .nil => 0
  | _, .snoc (middle := m) pre step =>
    if (getCurrentEpoch m.state).toNat ≤ high + 1 then
      PinDrift.Internal.netScan v high pre + PinDrift.Internal.stepNet v step
    else PinDrift.Internal.netScan v high pre

/-- The net credits to a key in the block steps of a run, after one more step. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.netScan_snoc (v high : ℕ) {x m y :
  ForkedBeaconState preset}
    (pre : Run config checks x m) (step : Step config checks m y) :
    PinDrift.Internal.netScan v high (pre.snoc step) =
      if (getCurrentEpoch m.state).toNat ≤ high + 1 then
        PinDrift.Internal.netScan v high pre + PinDrift.Internal.stepNet v step
      else PinDrift.Internal.netScan v high pre := rfl

/-- A run with no step has no net credits. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.netScan_nil (v high : ℕ) {x :
  ForkedBeaconState preset} :
    PinDrift.Internal.netScan v high (Run.nil : Run config checks x x) = 0 := rfl

/-- A run with no step has no credits to scan. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.creditScan_nil (blockP slotP :
  BalanceSource → Bool) (v high : ℕ)
    {x : ForkedBeaconState preset} :
    (PinDrift.Internal.creditScan blockP slotP v high (Run.nil : Run config checks x x)) = 0 := rfl

/-- Events within their credit limits credit the slashing events at most their limits. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.slashing_credits_le_limits (events
  : List (BalanceEvent preset))
    (bounded : ∀ e ∈ events, e.credits ≤ e.creditLimit) :
    ((events.filter (·.source = .slashings)).map BalanceEvent.credits).sum ≤
      (events.map fun e => if e.source = .slashings then e.creditLimit else 0).sum := by
  induction events with
  | nil => simp
  | cons head rest ih =>
    have tailLe := ih fun e member => bounded e (List.mem_cons_of_mem _ member)
    have headLe := bounded head List.mem_cons_self
    by_cases source : head.source = .slashings
    · simp only [List.filter_cons, source, decide_true, ↓reduceIte, List.map_cons, List.sum_cons]
      omega
    · simp only [List.filter_cons, source, decide_false, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.sum_cons]
      omega

end PinKeys

/-! ## A floor and a ceiling on one key's effective balance -/

namespace PinKeyFloor

open Base Uint64 Models

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- A successful update of the effective balances applies the scalar update at each index.

It reads the balance of the index, which it keeps. -/
private theorem effective_update_at {f : Fork} {s t : BeaconState preset f}
    (ok : processEffectiveBalanceUpdates s = .ok t) {i : ℕ}
    (inside : i < s.validators.data.size) :
    ∃ (v : Validator) (balance new : Gwei), s.validators.data[i]? = some v ∧
      s.balances.data[i]? = some balance ∧
      t.validators.data[i]? = some { v with effectiveBalance := new } ∧
      updatedEffectiveBalance preset (withdrawalMaxEffectiveBalance preset f v) balance
        v.effectiveBalance = .ok new := by
  have found : ∃ v, s.validators.data[i]? = some v :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  obtain ⟨v, found⟩ := found
  obtain ⟨balance, owned⟩ := processEffectiveBalanceUpdates_owned ok found
  obtain ⟨new, read, updated⟩ := processEffectiveBalanceUpdates_effectiveBalance_eq ok found owned
  exact ⟨v, balance, new, found, owned, read, updated⟩

/-- The update of the effective balances keeps a lower bound on the effective balance of a key.

Suppose the update changes the effective balance only if the balance rounded down is at least `low`.

Suppose also that the cap is at least `capLow`, and `low` is at most `capLow`.

The new value is the old one, or the balance rounded down to an increment, at most the cap. -/
private theorem effective_floor_update {f : Fork} {s t : BeaconState preset f}
    (ok : processEffectiveBalanceUpdates s = .ok t) (i capLow low : ℕ)
    (inside : i < s.validators.data.size) (lowCap : low ≤ capLow)
    (reach : (actualBalanceAt ⟨f, s⟩ i + preset.downwardBand < effectiveAt ⟨f, s⟩ i ∨
        effectiveAt ⟨f, s⟩ i + preset.upwardBand < actualBalanceAt ⟨f, s⟩ i) →
      low ≤ actualBalanceAt ⟨f, s⟩ i - actualBalanceAt ⟨f, s⟩ i %
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (previous : low ≤ effectiveAt ⟨f, s⟩ i)
    (cap : ∀ v, t.validators.data[i]? = some v →
      capLow ≤ (withdrawalMaxEffectiveBalance preset f v).toNat) :
    low ≤ effectiveAt ⟨f, t⟩ i := by
  obtain ⟨v, balance, new, found, owned, read, updated⟩ := effective_update_at ok inside
  have capped := cap _ read
  change capLow ≤ (withdrawalMaxEffectiveBalance preset f v).toNat at capped
  simp only [actualBalanceAt, owned, Option.map_some, Option.getD_some] at reach
  simp only [effectiveAt, found, Option.map_some, Option.getD_some] at reach previous
  simp only [effectiveAt, read, Option.map_some, Option.getD_some]
  rcases updatedEffectiveBalance_split updated with ⟨rfl, -⟩ | ⟨rfl, fires⟩
  · exact previous
  · rw [Base.Uint64.toNat_min, toNat_rounded]
    exact Nat.le_min.mpr ⟨reach fires, Nat.le_trans lowCap capped⟩

/-- One slot step keeps the lower bound, given the balance and the cap after it.

Only the epoch transition changes an effective balance, in its update. -/
private theorem effective_floor_slot {f : Fork} {s t : BeaconState preset f}
    (ok : advanceSlot config checks s = .ok t) (i capLow low : ℕ)
    (inside : i < s.validators.data.size) (lowCap : low ≤ capLow)
    (reach : (actualBalanceAt ⟨f, t⟩ i + preset.downwardBand < effectiveAt ⟨f, s⟩ i ∨
        effectiveAt ⟨f, s⟩ i + preset.upwardBand < actualBalanceAt ⟨f, t⟩ i) →
      low ≤ actualBalanceAt ⟨f, t⟩ i - actualBalanceAt ⟨f, t⟩ i %
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (previous : low ≤ effectiveAt ⟨f, s⟩ i)
    (cap : ∀ v, t.validators.data[i]? = some v →
      capLow ≤ (withdrawalMaxEffectiveBalance preset f v).toNat) :
    low ≤ effectiveAt ⟨f, t⟩ i := by
  have life := (registryLifecycle_advanceSlot ok).size_le
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨next, _, cached, cache, advanced, advance, rfl⟩ := ok
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cache
  unfold epochIfLast at advance
  split at advance
  · obtain ⟨before, after, kept, updated, validators, balances⟩ := balanceDrift_epoch advance
    have insideTail : i < advanced.validators.data.size := Nat.lt_of_lt_of_le inside life
    have insideBefore : i < before.validators.data.size := by
      rw [← (sameSizes_processEffectiveBalanceUpdates updated).1]
      rw [validators] at insideTail
      exact insideTail
    have prior : low ≤ effectiveAt ⟨f, before⟩ i := by
      rw [kept i inside]
      exact previous
    have bound := effective_floor_update updated i capLow low insideBefore lowCap
      (by
        rw [kept i inside]
        have reach' := reach
        simp only [actualBalanceAt, balances] at reach' ⊢
        exact reach') prior
      (fun v read => cap v (by rw [validators]; exact read))
    simpa only [effectiveAt, validators] using bound
  · cases advance
    exact previous

/-- The update of the effective balances keeps an upper bound on the effective balance of a key.

The smaller of the balance and `capHigh` must be at most `ceil`, and the cap at most `capHigh`.

The cap bound is a whole number of increments, and the old effective balance is at most it.

The new value is at most `ceil` plus the downward band.

It is also at most the old one, or the balance rounded down to an increment, at most the cap. -/
private theorem effective_ceiling_update {f : Fork} {s t : BeaconState preset f}
    (ok : processEffectiveBalanceUpdates s = .ok t) (i ceil capHigh : ℕ)
    (inside : i < s.validators.data.size)
    (alignedHigh : capHigh % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (old : effectiveAt ⟨f, s⟩ i ≤ capHigh)
    (funded : min (actualBalanceAt ⟨f, s⟩ i) capHigh ≤ ceil)
    (cap : ∀ v, t.validators.data[i]? = some v →
      (withdrawalMaxEffectiveBalance preset f v).toNat ≤ capHigh) :
    effectiveAt ⟨f, t⟩ i ≤ ceil + preset.downwardBand ∧
    effectiveAt ⟨f, t⟩ i ≤ max (effectiveAt ⟨f, s⟩ i)
      (min (ceil - ceil % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) capHigh) := by
  obtain ⟨v, balance, new, found, owned, read, updated⟩ := effective_update_at ok inside
  have capped := cap _ read
  change (withdrawalMaxEffectiveBalance preset f v).toNat ≤ capHigh at capped
  simp only [actualBalanceAt, owned, Option.map_some, Option.getD_some] at funded
  simp only [effectiveAt, found, Option.map_some, Option.getD_some] at old
  simp only [effectiveAt, read, found, Option.map_some, Option.getD_some]
  have add := updatedEffectiveBalance_le_add updated
  refine ⟨?_, ?_⟩
  · by_cases small : balance.toNat ≤ capHigh
    · omega
    · have newHigh : new.toNat ≤ capHigh := by
        rcases updatedEffectiveBalance_cases updated with rfl | rfl
        · exact old
        · rw [Base.Uint64.toNat_min, toNat_rounded]
          exact Nat.le_trans (Nat.min_le_right _ _) capped
      omega
  · rcases updatedEffectiveBalance_cases updated with rfl | rfl
    · exact Nat.le_max_left _ _
    · refine Nat.le_trans ?_ (Nat.le_max_right _ _)
      rw [Base.Uint64.toNat_min, toNat_rounded]
      by_cases small : balance.toNat ≤ capHigh
      · have funded' : balance.toNat ≤ ceil := by omega
        exact Nat.le_min.mpr ⟨Nat.le_trans (Nat.min_le_left _ _) (rounded_mono _ funded'),
          Nat.le_trans (Nat.min_le_right _ _) capped⟩
      · have ceilHigh : capHigh ≤ ceil := by omega
        have r := rounded_mono preset.EFFECTIVE_BALANCE_INCREMENT.toNat ceilHigh
        rw [alignedHigh, Nat.sub_zero] at r
        exact Nat.le_min.mpr ⟨Nat.le_trans (Nat.le_trans (Nat.min_le_right _ _) capped) r,
          Nat.le_trans (Nat.min_le_right _ _) capped⟩

/-- One slot step keeps an upper bound on the effective balance, given the balance and cap after it.

The step either keeps the effective balance and the epoch.

Or it moves to a later epoch, and the effective balance is at most `ceil` plus the band. -/
private theorem effective_ceiling_slot {f : Fork} {s t : BeaconState preset f}
    (ok : advanceSlot config checks s = .ok t) (i ceil capHigh : ℕ)
    (inside : i < s.validators.data.size)
    (alignedHigh : capHigh % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (old : effectiveAt ⟨f, s⟩ i ≤ capHigh)
    (funded : min (actualBalanceAt ⟨f, t⟩ i) capHigh ≤ ceil)
    (cap : ∀ v, t.validators.data[i]? = some v →
      (withdrawalMaxEffectiveBalance preset f v).toNat ≤ capHigh) :
    effectiveAt ⟨f, t⟩ i ≤ max (effectiveAt ⟨f, s⟩ i)
      (min (ceil - ceil % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) capHigh) ∧
    ((effectiveAt ⟨f, t⟩ i = effectiveAt ⟨f, s⟩ i ∧
        (getCurrentEpoch t).toNat = (getCurrentEpoch s).toNat) ∨
      (effectiveAt ⟨f, t⟩ i ≤ ceil + preset.downwardBand ∧
        (getCurrentEpoch s).toNat < (getCurrentEpoch t).toNat)) := by
  obtain ⟨next, cached, epoched, sum, cache, edge, rfl⟩ := advanceSlot_ok ok
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cache
  rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
  have cases : ∀ c : BeaconState preset f, epochIfLast config checks next c = .ok epoched →
      next % preset.SLOTS_PER_EPOCH = 0 ∧ processEpoch config checks c = .ok epoched ∨
      next % preset.SLOTS_PER_EPOCH ≠ 0 ∧ epoched = c := by
    intro c edge
    unfold epochIfLast at edge
    split at edge
    · exact .inl ⟨‹_›, edge⟩
    · exact .inr ⟨‹_›, (Except.ok.inj edge).symm⟩
  rcases cases _ edge with ⟨boundary, epoch⟩ | ⟨inner, rfl⟩
  · obtain ⟨before, after, kept, updated, validators, balances⟩ := balanceDrift_epoch epoch
    have insideTail : i < epoched.validators.data.size := by
      have := (registryLifecycle_advanceSlot ok).size_le
      simpa using Nat.lt_of_lt_of_le inside this
    have insideBefore : i < before.validators.data.size := by
      rw [← (sameSizes_processEffectiveBalanceUpdates updated).1]
      rw [validators] at insideTail
      exact insideTail
    have bound := effective_ceiling_update updated i ceil capHigh insideBefore alignedHigh
      (by rw [kept i inside]; exact old)
      (by simpa only [actualBalanceAt, balances] using funded)
      (fun v read => cap v (by rw [validators]; exact read))
    have e := nextSlot_epoch_of_boundary sum boundary
    refine ⟨?_, .inr ⟨?_, ?_⟩⟩
    · have := bound.2
      rw [kept i inside] at this
      simpa only [effectiveAt, validators] using this
    · simpa only [effectiveAt, validators] using bound.1
    · simp only
      omega
  · refine ⟨?_, .inl ⟨rfl, ?_⟩⟩
    · exact Nat.le_max_left _ _
    · simp only
      rw [nextSlot_epoch_of_inside sum inner]

section Rewards

open DirectSafety PinKeys

/-! ### One key's reward in an epoch pass -/

/-- The epoch-pass reward credits to the key in one step.

A slot step's events are those of its epoch pass and its upgrades.

So its `.rewards` events are the epoch's rewards.

A block step has none counted: its proposer credits are charged elsewhere. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.epochRewards (v : ℕ) {x y :
  ForkedBeaconState preset}
    (step : Step config checks x y) : ℕ :=
  match step with
  | .slot ok =>
    ((((Step.slot (config := config) (checks := checks) ok).balanceEvents.toOption.getD []).filter
      (·.source = .rewards)).map (PinDrift.Internal.keyCredit v)).sum
  | .block .. => 0

/-- The reward credits of a list of events are those of the events, read at one position. -/
private theorem sum_filter_rewards (events : List (BalanceEvent preset)) (v : ℕ) :
    ((events.filter (·.source = .rewards)).map (PinDrift.Internal.keyCredit v)).sum =
      (events.map (DirectSafety.Apriori.Internal.rewardCredit v)).sum := by
  induction events with
  | nil => rfl
  | cons e rest ih =>
    by_cases rewards : e.source = .rewards
    · simp [rewards, PinDrift.Internal.keyCredit, DirectSafety.Apriori.Internal.rewardCredit, ih]
    · simp [rewards, DirectSafety.Apriori.Internal.rewardCredit, ih]

/-- A flag pays a key at most its base reward times the weight of the flag, over the active stake.

The increments that set the flag in the previous epoch are at most those active then.

The rate read there is at most `P` times the active increments.

A key that is not active in the previous epoch earns nothing, so it needs no rate.

That is also stated outright, as its reward being 0. -/
private theorem flagReward_le {f : Fork} (altair : .altair ≤ f) {state : BeaconState preset f}
    (within : state.RegistryWithinLimit) {flag : Fin PARTICIPATION_FLAG_WEIGHTS.length}
    {rewards penalties : Array Gwei}
    (computed : getFlagIndexDeltas state altair flag = .ok (rewards, penalties))
    {total : Gwei} (active : getTotalActiveBalance state = .ok total) (P v : ℕ)
    (inside : v < state.validators.data.size)
    (rate : v.toUInt64 ∉ getActiveValidatorIndices state (getPreviousEpoch state) ∨
      ∀ perIncrement : Gwei, getBaseRewardPerIncrement preset total = .ok perIncrement →
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
      (rewards.getD v 0).toNat = 0) ∧
    (v.toUInt64 ∉ getActiveValidatorIndices state (getPreviousEpoch state) →
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
        (rewards.getD v 0).toNat = 0) ∧
      (v.toUInt64 ∉ getActiveValidatorIndices state (getPreviousEpoch state) →
        (rewards.getD v 0).toNat = 0) :=
    ⟨by rw [h, Nat.zero_mul]; exact Nat.zero_le _, fun _ => h, fun _ => h⟩
  by_cases isEligible : eligible = true
  swap
  · exact zero (by simp [(notEligible (by simpa using isEligible)).1])
  obtain ⟨base, baseOk, member⟩ := eligibleCase isEligible
  by_cases present : v.toUInt64 ∈ participating
  swap
  · exact zero (by simp [(member.2 present).1])
  have rate := rate.resolve_left fun idle =>
    idle (mem_getUnslashedParticipatingIndices flaggedOk _ present).1
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
  refine ⟨?_, fun none => by rw [formula, none, Nat.zero_mul, Nat.div_zero],
    fun idle => absurd (mem_getUnslashedParticipatingIndices flaggedOk _ present).1 idle⟩
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

A state with no active increment pays nothing.

A key that is not active in the previous epoch is paid nothing. -/
private theorem replayRewards_credit_le {f : Fork} (altair : .altair ≤ f)
    {pass : BeaconState preset f} (within : pass.RegistryWithinLimit)
    {rewarded : BalanceReplay preset f}
    (replayed : replayRewards (config := config) (pass, []) = .ok rewarded) (P v : ℕ)
    (inside : v < pass.validators.data.size)
    (rate : v.toUInt64 ∉ getActiveValidatorIndices pass (getPreviousEpoch pass) ∨
      ∀ total perIncrement : Gwei, getTotalActiveBalance pass = .ok total →
        getBaseRewardPerIncrement preset total = .ok perIncrement →
        perIncrement.toNat *
            ((∑ i ∈ (getActiveValidatorIndices pass (getPreviousEpoch pass)).toFinset,
              balanceAt pass i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
          P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) :
    (rewarded.2.map (DirectSafety.Apriori.Internal.rewardCredit v)).sum = 0 ∨
      ∃ total : Gwei,
        (rewarded.2.map (DirectSafety.Apriori.Internal.rewardCredit v)).sum *
            (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * 64) ≤
          balanceAt pass v / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * 54 *
            (P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ∧
        (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 →
          (rewarded.2.map (DirectSafety.Apriori.Internal.rewardCredit v)).sum = 0) ∧
        (v.toUInt64 ∉ getActiveValidatorIndices pass (getPreviousEpoch pass) →
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
      computed active P v inside (rate.imp_right fun rate per perOk => rate total per active perOk)
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
  obtain ⟨b1, z1, i1⟩ := one
  obtain ⟨b2, z2, i2⟩ := two
  obtain ⟨b3, z3, i3⟩ := three
  refine .inr ⟨total, ?_, fun none => ?_, fun idle => ?_⟩
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
  · have := i1 idle
    have := i2 idle
    have := i3 idle
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

/-- The rewards replay credits no key past the registry.

It records an increase or a decrease at an index that the registry holds, and keeps its sizes. -/
private theorem replayRewards_absent {f : Fork} {pass : BeaconState preset f}
    {rewarded : BalanceReplay preset f}
    (replayed : replayRewards (config := config) (pass, []) = .ok rewarded)
    (matched : BalancesMatch pass) {v : ℕ} (outside : pass.validators.data.size ≤ v) :
    (rewarded.2.map (DirectSafety.Apriori.Internal.rewardCredit v)).sum = 0 := by
  have final := replayRewards_induction (config := config)
    (fun pre : BalanceReplay preset f => BalancesMatch pre.1 ∧
      pre.1.validators = pass.validators ∧
        (pre.2.map (DirectSafety.Apriori.Internal.rewardCredit v)).sum = 0)
    (fun {pre post index reward} held ok => by
      obtain ⟨_, _, _, actionOk, events⟩ := recordBalance_single ok
      rw [events]
      have increased := liftAccessor_ok.mp actionOk
      have same := sameSizes_increaseBalance increased
      have registry := increaseBalance_validators increased
      obtain ⟨preMatched, preSame, preSum⟩ := held
      have preSize : pre.1.balances.data.size ≤ v := by
        unfold BalancesMatch at preMatched
        rw [preMatched, preSame]
        exact outside
      refine ⟨balancesMatch_of_sameSizes same preMatched, registry.trans preSame, ?_⟩
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, preSum, DirectSafety.Apriori.Internal.rewardCredit, ↓reduceIte,
        actualBalanceAt, Array.getElem?_eq_none preSize,
        Array.getElem?_eq_none (show post.1.balances.data.size ≤ v by rw [same.2]; exact preSize),
        Option.map_none,
        Option.getD_none, Nat.sub_self, Nat.add_zero])
    (fun {source pre post index penalty} sourceCases held ok => by
      obtain ⟨_, _, _, actionOk, events⟩ := recordBalance_single ok
      rw [events]
      have decreased := liftAccessor_ok.mp actionOk
      have same := sameSizes_decreaseBalance decreased
      have registry := decreaseBalance_validators decreased
      obtain ⟨preMatched, preSame, preSum⟩ := held
      refine ⟨balancesMatch_of_sameSizes same preMatched, registry.trans preSame, ?_⟩
      rcases sourceCases with rfl | rfl <;>
        simp [List.map_append, List.sum_append, preSum,
          DirectSafety.Apriori.Internal.rewardCredit])
    ⟨matched, rfl, rfl⟩ replayed
  exact final.2.2

open DirectSafety.Apriori.Internal in
/-- One key's rewards credit in a step is at most a rate for each epoch that the step ends.

The step is a slot, and it ends an epoch exactly when it runs the epoch's pass.

The key's stake at the start is at most `E`.

`P` bounds the rate read at the active stake, scaled by the previous epoch's share of it.

A key past the registry of a state with matched balances gets no reward. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.epochRewards_le {m n :
  ForkedBeaconState preset}
    (step : Step config checks m n) (altair : .altair ≤ m.fork) (early : n.fork < .glamsterdam)
    (v : ℕ) (known : v < m.state.validators.data.size ∨ BalancesMatch m.state) (E P : ℕ)
    (envelope : v.toUInt64 ∉ getActiveValidatorIndices m.state (getPreviousEpoch m.state) ∨
      effectiveAt m v ≤ E)
    (rate : v.toUInt64 ∉ getActiveValidatorIndices m.state (getPreviousEpoch m.state) ∨
      ∀ total perIncrement : Gwei, getTotalActiveBalance m.state = .ok total →
        getBaseRewardPerIncrement preset total = .ok perIncrement →
        perIncrement.toNat *
            ((∑ i ∈ (getActiveValidatorIndices m.state (getPreviousEpoch m.state)).toFinset,
              effectiveAt m i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
          P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) :
    PinDrift.Internal.epochRewards v step ≤ ((getCurrentEpoch n.state).toNat - (getCurrentEpoch
      m.state).toNat) *
      (E / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) := by
  cases step with
  | block engine signed due ok => simp [PinDrift.Internal.epochRewards]
  | slot ok =>
    have mEarly : m.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (Step.slot ok).chainStep.fork_le early
    simp only [PinDrift.Internal.epochRewards]
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
      -- A key past the registry gets no reward, as the replay keeps the sizes of the balances.
      by_cases inside : v < m.state.validators.data.size
      swap
      · have matched := known.resolve_left inside
        have passBalances : pass.balances = m.state.balances := by
          have first := justified.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
          have second := scored.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
          obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
          exact second.2.1.trans first.2.1
        rw [replayRewards_absent rewardedOk (by
          unfold BalancesMatch at matched ⊢
          rw [passBalances, validatorsEq]
          exact matched) (by rw [validatorsEq]; omega)]
        exact Nat.zero_le _
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
      have ratePass : v.toUInt64 ∉ getActiveValidatorIndices pass (getPreviousEpoch pass) ∨
          ∀ total perIncrement : Gwei, getTotalActiveBalance pass = .ok total →
            getBaseRewardPerIncrement preset total = .ok perIncrement →
            perIncrement.toNat *
                ((∑ i ∈ (getActiveValidatorIndices pass (getPreviousEpoch pass)).toFinset,
                  balanceAt pass i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
              P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
        rw [prevEq]
        refine rate.imp_right fun rate total perIncrement totalOk perOk => ?_
        have sums : (∑ i ∈ (getActiveValidatorIndices m.state (getPreviousEpoch m.state)).toFinset,
            balanceAt pass i.toNat) =
            ∑ i ∈ (getActiveValidatorIndices m.state (getPreviousEpoch m.state)).toFinset,
              effectiveAt m i.toNat :=
          Finset.sum_congr rfl fun i _ => balanceAtEq i.toNat
        rw [sums]
        exact rate total perIncrement (totalEq.symm.trans totalOk) perOk
      have bound := replayRewards_credit_le altair within rewardedOk P v insidePass ratePass
      have flagSum : (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum = 54 := rfl
      have wd : WEIGHT_DENOMINATOR.toNat = 64 := by decide
      rw [flagSum, wd]
      rcases bound with zero | ⟨total, scaled, none, idle⟩
      · rw [zero]
        exact Nat.zero_le _
      rcases envelope with inactive | envelope
      · rw [idle (by rw [prevEq]; exact inactive)]
        exact Nat.zero_le _
      · exact reward_sum_le _ _ _ _ P scaled none (Nat.div_le_div_right (by
          rw [balanceAtEq]
          exact envelope))

/-- A step raises the balance of a key by at most the credits of its events. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.step_balance_le_events {m n :
  ForkedBeaconState preset}
    (step : Step config checks m n) (early : n.fork < .glamsterdam) (i : ℕ)
    {events : List (BalanceEvent preset)} (ok : step.balanceEvents = .ok events) :
    actualBalanceAt n i ≤ actualBalanceAt m i + (events.map (PinDrift.Internal.keyCredit i)).sum :=
      by
  have run := DirectSafety.Apriori.Internal.single_balanceEvents step ok
  have cover := coverage_run (Run.nil.snoc step) early (getCurrentEpoch n.state).toNat
    (Nat.le_succ _) run false i
  have ends := Run.balancePath_ends (Run.nil.snoc step)
  have rise := Apriori.Internal.balance_le_pathCredits i _ m n ends.1 ends.2
  simp only [coveragePath, Bool.false_eq_true, ↓reduceIte, coverageDelta] at cover
  exact le_trans rise (Nat.add_le_add_left cover _)

/-- A step raises the balance of a key by at most its epoch rewards and its other credits.

A block step counts the rise of the key's balance across the whole step.

A slot step counts the credits of its events from the sources other than the epoch rewards. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.step_balance_le {m n :
  ForkedBeaconState preset} (step : Step config checks m n)
    (early : n.fork < .glamsterdam) (i : ℕ) :
    actualBalanceAt n i ≤ actualBalanceAt m i + PinDrift.Internal.epochRewards i step +
      PinDrift.Internal.stepNet i step + PinDrift.Internal.stepCredit (fun _ => false) (fun s =>
        decide (s ≠ .rewards)) i step := by
  cases step with
  | block engine signed due okb =>
    simp only [PinDrift.Internal.epochRewards, PinDrift.Internal.stepNet]
    omega
  | slot oks =>
    obtain ⟨events, ok⟩ := (Step.slot oks : Step config checks m n).balanceEvents_ok early
    have base := PinDrift.Internal.step_balance_le_events (Step.slot oks : Step config checks m n)
      early i ok
    simp only [PinDrift.Internal.epochRewards, PinDrift.Internal.stepNet,
      PinDrift.Internal.stepCredit, ok, Except.toOption, Option.getD_some] at base ⊢
    have split := List.sum_map_filter_add_sum_map_filter_not
      (fun e : BalanceEvent preset => e.source = .rewards) (PinDrift.Internal.keyCredit i) events
    simp only [ne_eq] at split ⊢
    omega

/-- The bound on a key's balance below a cap along a run.

It is the start, the epoch rewards and the other credits.

The start and the balance count only up to the cap.

The epoch rewards are those of the epochs that the run ends, at the rate given by `E` and `P`.

The other credits are the net rises of its block steps and the credits of its slot steps.

The slot-step credits leave out the epoch rewards. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.creditBound {x y : ForkedBeaconState
  preset} (tail : Run config checks x y)
    (i high E P capHigh : ℕ) : ℕ :=
  min (actualBalanceAt x i) capHigh +
    ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) *
      (E / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) +
    PinDrift.Internal.netScan i high tail +
      (PinDrift.Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high tail)

end Rewards

/-- A balance ceiling, an envelope or a floor on a key's balance bounds its effective balance.

First, suppose a key's balance stays at least `floor` at every state of the run.

Suppose also that its cap stays at least `capLow`.

Then its effective balance at the end is at least the least of three values.

They are its effective balance at the start, `capLow`, and `floor` rounded down to an increment.

Second, suppose the effective balance at the start is a whole number of increments.

Suppose a step that could lower it leaves a balance of at least that effective balance.

A step could lower it when the balance after it plus the downward band is below it.

Suppose also that its cap stays at least its effective balance at the start.

Then the effective balance at the end is at least that at the start.

A downward update sets it to the balance rounded down.

That is at least the effective balance at the start, which is a whole number of increments.

An update moves the effective balance only at an epoch's first slot.

It moves it down to the balance rounded to an increment, and up to at most the cap.

It never moves it up below where it was.

Third, suppose the smaller of the balance and `capHigh` stays at most `ceil`.

Suppose also that the cap stays at most `capHigh`.

The bound `capHigh` is a whole number of increments.

The effective balance at the start is at most `capHigh`.

Then the effective balance at the end is at most the greater of two values.

They are its effective balance at the start, and the ceiling rounded down, at most the cap.

If no epoch boundary is crossed, it is the effective balance at the start.

After a boundary, it is at most `ceil` plus the downward band.

The epoch never moves back.

Fourth, suppose the cap stays at most `capHigh`, as in the third.

Suppose the rate of the rewards at every state is at most `P`.

Suppose also that the run ends by the epoch `high + 1`.

Suppose also that `E` is at least the greatest effective balance that the bound below allows.

Then the balance at every state is at most its start, plus the epoch rewards at the rate of `E`.

It also adds the other credits that the events of the run give the key. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Run.effective_floor_pair {x y :
  ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ x.fork)
    (i : ℕ) (inside : i < x.state.validators.data.size)
    (floor capLow capHigh high E P : ℕ) :
    ((∀ z ∈ tail.balancePath, floor ≤ actualBalanceAt z i) →
      (∀ z ∈ tail.balancePath, capLow ≤ PinTerms.capAt z i) →
      min (effectiveAt x i)
        (min capLow (floor - floor % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
          effectiveAt y i) ∧
    (effectiveAt x i % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 →
      (∀ {m n : ForkedBeaconState preset} (before : Run config checks x m)
          (step : Step config checks m n) (after : Run config checks n y),
        (before.snoc step).append after = tail →
        actualBalanceAt n i + preset.downwardBand < effectiveAt m i →
        effectiveAt x i ≤ actualBalanceAt n i) →
      (∀ z ∈ tail.balancePath, effectiveAt x i ≤ PinTerms.capAt z i) →
      effectiveAt x i ≤ effectiveAt y i) ∧
    (∀ ceil : ℕ, capHigh % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 →
      effectiveAt x i ≤ capHigh →
      (∀ z ∈ tail.balancePath, min (actualBalanceAt z i) capHigh ≤ ceil) →
      (∀ z ∈ tail.balancePath, PinTerms.capAt z i ≤ capHigh) →
      effectiveAt y i ≤ max (effectiveAt x i)
        (min (ceil - ceil % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) capHigh) ∧
      ((getCurrentEpoch y.state).toNat ≤ (getCurrentEpoch x.state).toNat →
        effectiveAt y i = effectiveAt x i) ∧
      ((getCurrentEpoch x.state).toNat < (getCurrentEpoch y.state).toNat →
        effectiveAt y i ≤ ceil + preset.downwardBand) ∧
      (getCurrentEpoch x.state).toNat ≤ (getCurrentEpoch y.state).toNat) ∧
    (capHigh % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 → effectiveAt x i ≤ capHigh →
      (∀ z ∈ tail.balancePath, PinTerms.capAt z i ≤ capHigh) →
      (∀ z ∈ tail.balancePath,
        i.toUInt64 ∉ getActiveValidatorIndices z.state (getPreviousEpoch z.state) ∨
        ∀ total perIncrement : Gwei,
          getTotalActiveBalance z.state = .ok total →
          getBaseRewardPerIncrement preset total = .ok perIncrement →
          perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices z.state
            (getPreviousEpoch z.state)).toFinset, effectiveAt z j.toNat) /
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
            P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) →
      (getCurrentEpoch y.state).toNat ≤ high + 1 →
      max (effectiveAt x i) (min capHigh (PinDrift.Internal.creditBound tail i high E P capHigh -
        PinDrift.Internal.creditBound tail i high E P capHigh %
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ E →
      ∀ z ∈ tail.balancePath, min (actualBalanceAt z i) capHigh ≤
        PinDrift.Internal.creditBound tail i high E P capHigh) := by
  induction tail with
  | nil => exact ⟨fun _ _ => Nat.min_le_left _ _, fun _ _ _ => Nat.le_refl _,
      fun _ _ _ _ _ => ⟨Nat.le_max_left _ _, fun _ => rfl, fun h => absurd h (Nat.lt_irrefl _),
        Nat.le_refl _⟩,
      fun _ _ _ _ _ _ z hz => by
        rw [Run.balancePath, List.mem_singleton] at hz
        subst hz
        simp [PinDrift.Internal.creditBound, PinDrift.Internal.netScan_nil,
          PinDrift.Internal.creditScan_nil]⟩
  | @snoc middle last pre step ih =>
    have middleEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
    obtain ⟨ihFloor, ihEnvelope, ihCeiling, ihCredit⟩ := ih middleEarly
    have room : i < middle.state.validators.data.size :=
      Nat.lt_of_lt_of_le inside pre.registryLifecycle.size_le
    have atMiddle : middle ∈ pre.balancePath :=
      List.mem_of_mem_getLast? (Run.balancePath_ends pre).2
    have altair : .altair ≤ middle.fork :=
      Nat.le_trans (by decide) (Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps))
    have key : capHigh % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 → effectiveAt x i ≤ capHigh →
        (∀ z ∈ (pre.snoc step).balancePath, PinTerms.capAt z i ≤ capHigh) →
        (∀ z ∈ (pre.snoc step).balancePath,
          i.toUInt64 ∉ getActiveValidatorIndices z.state (getPreviousEpoch z.state) ∨
          ∀ total perIncrement : Gwei,
            getTotalActiveBalance z.state = .ok total →
            getBaseRewardPerIncrement preset total = .ok perIncrement →
            perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices z.state
              (getPreviousEpoch z.state)).toFinset, effectiveAt z j.toNat) /
                preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
              P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) →
        (getCurrentEpoch last.state).toNat ≤ high + 1 →
        max (effectiveAt x i) (min capHigh (PinDrift.Internal.creditBound (pre.snoc step) i high E P
          capHigh -
          PinDrift.Internal.creditBound (pre.snoc step) i high E P capHigh %
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ E →
        (∀ z ∈ step.balancePath, z = middle ∨ z = last) →
        ∀ z ∈ (pre.snoc step).balancePath,
          min (actualBalanceAt z i) capHigh ≤ PinDrift.Internal.creditBound (pre.snoc step) i high E
            P capHigh := by
      intro alignedHigh startCap capC rate endEp closed pathCases z hz
      have xm : (getCurrentEpoch x.state).toNat ≤ (getCurrentEpoch middle.state).toNat :=
        UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
      have ml : (getCurrentEpoch middle.state).toNat ≤ (getCurrentEpoch last.state).toNat :=
        UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
      have within : (getCurrentEpoch middle.state).toNat ≤ high + 1 := by omega
      have scan := PinDrift.Internal.creditScan_snoc (fun _ => false) (fun s => decide (s ≠
        .rewards))
        i high pre step
      have net := PinDrift.Internal.netScan_snoc i high pre step
      simp only [within, ↓reduceIte] at scan net
      have tailEq : PinDrift.Internal.creditBound (pre.snoc step) i high E P capHigh =
          PinDrift.Internal.creditBound pre i high E P capHigh +
            ((getCurrentEpoch last.state).toNat - (getCurrentEpoch middle.state).toNat) *
              (E / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
                (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) +
            (PinDrift.Internal.stepNet i step +
              PinDrift.Internal.stepCredit (fun _ => false) (fun s => decide (s ≠ .rewards)) i step)
                := by
        unfold PinDrift.Internal.creditBound
        rw [scan, net]
        generalize E / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat = G
        have split : ((getCurrentEpoch last.state).toNat - (getCurrentEpoch x.state).toNat) * G =
            ((getCurrentEpoch middle.state).toNat - (getCurrentEpoch x.state).toNat) * G +
              ((getCurrentEpoch last.state).toNat - (getCurrentEpoch middle.state).toNat) * G := by
          rw [← Nat.add_mul]
          congr 1
          omega
        rw [split]
        omega
      have closedPre : max (effectiveAt x i) (min capHigh (PinDrift.Internal.creditBound pre i high
        E P capHigh -
          PinDrift.Internal.creditBound pre i high E P capHigh %
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ E :=
        le_trans (max_le_max le_rfl (min_le_min le_rfl (rounded_mono _ (by omega)))) closed
      have ihPre := ihCredit alignedHigh startCap
        (fun p member => capC p (List.mem_append_left _ member))
        (fun p member => rate p (List.mem_append_left _ member)) within closedPre
      rcases List.mem_append.mp hz with old | stepMember
      · exact (ihPre z old).trans (by omega)
      · rcases pathCases z stepMember with rfl | rfl
        · exact (ihPre _ atMiddle).trans (by omega)
        · have ceilings : ∀ p ∈ pre.balancePath,
              min (actualBalanceAt p i) capHigh ≤ PinDrift.Internal.creditBound (pre.snoc step) i
                high E P capHigh :=
            fun p member => (ihPre p member).trans (by omega)
          obtain ⟨c1, -, -, -⟩ := ihCeiling (PinDrift.Internal.creditBound (pre.snoc step) i high E
            P capHigh)
            alignedHigh startCap ceilings
            (fun p member => capC p (List.mem_append_left _ member))
          rw [Nat.min_comm] at c1
          have envelope : effectiveAt middle i ≤ E := c1.trans closed
          have rewards := PinDrift.Internal.epochRewards_le step altair early i (Or.inl room) E P
            (.inr envelope)
            (rate middle (List.mem_append_left _ atMiddle))
          have stepBound := PinDrift.Internal.step_balance_le step early i
          have mid := ihPre _ atMiddle
          rw [tailEq]
          omega
    cases step with
    | @block fork before after engine signed due ok =>
      have kept := effectiveKept_processBlock (applySignedBlock_ok ok).2.1 i room
      have epoch : (getCurrentEpoch after).toNat = (getCurrentEpoch before).toNat := by
        simp only [getCurrentEpoch, processBlock_slot (applySignedBlock_ok ok).2.1]
      refine ⟨fun balanceFloor capFloor => ?_, fun aligned downs capFloor => ?_,
        fun ceil alignedHigh startCap balanceCeil capCeil => ?_,
        fun alignedHigh startCap capC rate endEp closed =>
          key alignedHigh startCap capC rate endEp closed
            (fun z hz => by simpa [Step.balancePath] using hz)⟩
      · rw [kept]
        exact ihFloor (fun p member => balanceFloor p (List.mem_append_left _ member))
          (fun p member => capFloor p (List.mem_append_left _ member))
      · rw [kept]
        exact ihEnvelope aligned
          (fun r1 st r2 cut => downs r1 st (r2.snoc (Step.block engine signed due ok))
            (congrArg (fun r => Run.snoc r (Step.block engine signed due ok)) cut))
          (fun p member => capFloor p (List.mem_append_left _ member))
      · obtain ⟨c1, c2, c3, c4⟩ := ihCeiling ceil alignedHigh startCap
          (fun p member => balanceCeil p (List.mem_append_left _ member))
          (fun p member => capCeil p (List.mem_append_left _ member))
        simp only at epoch c2 c3 c4 ⊢
        rw [kept, epoch]
        exact ⟨c1, c2, c3, c4⟩
    | slot ok =>
      obtain ⟨next, advanced, upgraded⟩ := bind_ok_iff.mp ok
      have onPath : (⟨middle.fork, next⟩ : ForkedBeaconState preset) ∈
          (Step.slot ok).balancePath := by
        simp [Step.balancePath, advanced, Except.toOption]
      have fuluMiddle : Fork.fusaka ≤ middle.fork :=
        Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps)
      have same := DirectSafety.Apriori.Internal.processUpgrades_eq_of_window upgraded
        fuluMiddle early
      subst same
      refine ⟨fun balanceFloor capFloor => ?_, fun aligned downs capFloor => ?_,
        fun ceil alignedHigh startCap balanceCeil capCeil => ?_,
        fun alignedHigh startCap capC rate endEp closed =>
          key alignedHigh startCap capC rate endEp closed
            (fun z hz => by simpa [Step.balancePath, advanced, Except.toOption] using hz)⟩
      · have funded := balanceFloor _ (List.mem_append_right _ onPath)
        have capped := capFloor _ (List.mem_append_right _ onPath)
        have prior := ihFloor (fun p member => balanceFloor p (List.mem_append_left _ member))
          (fun p member => capFloor p (List.mem_append_left _ member))
        refine effective_floor_slot advanced i capLow _ room
          (Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)) (fun _ => ?_) prior
          (fun v read => by simpa [PinTerms.capAt, read] using capped)
        exact (Nat.min_le_right _ _).trans ((Nat.min_le_right _ _).trans (rounded_mono _ funded))
      · have capped := capFloor _ (List.mem_append_right _ onPath)
        have prior := ihEnvelope aligned
          (fun r1 st r2 cut => downs r1 st (r2.snoc (Step.slot ok))
            (congrArg (fun r => Run.snoc r (Step.slot ok)) cut))
          (fun p member => capFloor p (List.mem_append_left _ member))
        refine effective_floor_slot advanced i (PinTerms.capAt ⟨middle.fork, next⟩ i) _ room capped
          (fun fires => ?_) prior (fun v read => by simp [PinTerms.capAt, read])
        have eta : effectiveAt (⟨middle.fork, middle.state⟩ : ForkedBeaconState preset) i =
            effectiveAt middle i := rfl
        rw [eta] at fires
        have reach : effectiveAt x i ≤ actualBalanceAt ⟨middle.fork, next⟩ i := by
          rcases fires with below | above
          · exact downs pre (Step.slot ok) Run.nil rfl below
          · omega
        have lift := rounded_mono preset.EFFECTIVE_BALANCE_INCREMENT.toNat reach
        rw [aligned, Nat.sub_zero] at lift
        exact lift
      · have funded := balanceCeil _ (List.mem_append_right _ onPath)
        have capped := capCeil _ (List.mem_append_right _ onPath)
        obtain ⟨c1, c2, c3, c4⟩ := ihCeiling ceil alignedHigh startCap
          (fun p member => balanceCeil p (List.mem_append_left _ member))
          (fun p member => capCeil p (List.mem_append_left _ member))
        have oldHigh : effectiveAt (⟨middle.fork, middle.state⟩ : ForkedBeaconState preset) i ≤
            capHigh := by
          have eta : effectiveAt (⟨middle.fork, middle.state⟩ : ForkedBeaconState preset) i =
              effectiveAt middle i := rfl
          rw [eta]
          omega
        obtain ⟨d1, d2⟩ := effective_ceiling_slot advanced i ceil capHigh room alignedHigh oldHigh
          funded (fun v read => by simpa [PinTerms.capAt, read] using capped)
        simp only at c1 c2 c3 c4 d1 d2 ⊢
        have eta : effectiveAt (⟨middle.fork, middle.state⟩ : ForkedBeaconState preset) i =
            effectiveAt middle i := rfl
        rw [eta] at d1 d2
        generalize min (ceil - ceil % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) capHigh = bound
          at c1 d1 ⊢
        rcases d2 with ⟨keep, same⟩ | ⟨rise, later⟩
        · refine ⟨by omega, fun h => ?_, fun h => ?_, by omega⟩
          · rw [keep]
            exact c2 (by omega)
          · rw [keep]
            exact c3 (by omega)
        · refine ⟨by omega, fun h => by omega, fun _ => rise, by omega⟩

/-- A balance floor and a cap floor along a run give an effective-balance floor, rounded.

Its effective balance at the end is at least the least of three values.

They are its effective balance at the start, `capLow`, and `floor` rounded down to an increment. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Run.effective_floor_rounded {x y :
  ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ x.fork)
    (i : ℕ) (inside : i < x.state.validators.data.size) (floor capLow : ℕ)
    (balanceFloor : ∀ z ∈ tail.balancePath, floor ≤ actualBalanceAt z i)
    (capFloor : ∀ z ∈ tail.balancePath, capLow ≤ PinTerms.capAt z i) :
    min (effectiveAt x i) (min capLow (floor - floor % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
      effectiveAt y i :=
  (PinDrift.Internal.Run.effective_floor_pair tail early fulu i inside floor capLow 0 0 0 0).1
    balanceFloor
    capFloor

/-- A balance floor and a cap floor along a run give an effective-balance floor.

Suppose a key's balance stays at least `floor` at every state of a run.

Suppose also that its cap stays at least `capLow`.

Then its effective balance at the end is at least the least of three values.

They are its effective balance at the start, `capLow`, and `floor` less one increment of rounding.

This follows from `Run.effective_floor_rounded`.

The floor rounded down to an increment is at least `floor + 1 - inc`. -/
private theorem Run.effective_floor_of_balance_floor {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ x.fork)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (i : ℕ)
    (inside : i < x.state.validators.data.size) (floor capLow : ℕ)
    (balanceFloor : ∀ z ∈ tail.balancePath, floor ≤ actualBalanceAt z i)
    (capFloor : ∀ z ∈ tail.balancePath, capLow ≤ PinTerms.capAt z i) :
    min (effectiveAt x i) (min capLow (floor + 1 - preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
      effectiveAt y i := by
  have remainder := Nat.mod_lt floor incPos
  refine Nat.le_trans ?_
    (PinDrift.Internal.Run.effective_floor_rounded tail early fulu i inside floor capLow
      balanceFloor capFloor)
  omega

/-- A balance ceiling and a cap ceiling along a run give an effective-balance ceiling.

Suppose the smaller of a key's balance and `capHigh` stays at most `ceil` along a run.

Suppose also that its cap stays at most `capHigh`.

The bound `capHigh` is a whole number of increments.

The effective balance at the start is at most `capHigh`.

Then its effective balance at the end is at most the greater of two values.

They are its effective balance at the start, and the ceiling rounded down, at most the cap.

If no epoch boundary is crossed, it is the effective balance at the start.

After a boundary, it is at most `ceil` plus the downward band.

The epoch never moves back. -/
theorem
  _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Run.effective_ceiling_of_balance_ceiling
  {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ x.fork)
    (i : ℕ) (inside : i < x.state.validators.data.size) (ceil capHigh : ℕ)
    (alignedHigh : capHigh % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (startCap : effectiveAt x i ≤ capHigh)
    (balanceCeil : ∀ z ∈ tail.balancePath, min (actualBalanceAt z i) capHigh ≤ ceil)
    (capCeil : ∀ z ∈ tail.balancePath, PinTerms.capAt z i ≤ capHigh) :
    effectiveAt y i ≤ max (effectiveAt x i)
      (min (ceil - ceil % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) capHigh) ∧
    ((getCurrentEpoch y.state).toNat ≤ (getCurrentEpoch x.state).toNat →
      effectiveAt y i = effectiveAt x i) ∧
    ((getCurrentEpoch x.state).toNat < (getCurrentEpoch y.state).toNat →
      effectiveAt y i ≤ ceil + preset.downwardBand) ∧
    (getCurrentEpoch x.state).toNat ≤ (getCurrentEpoch y.state).toNat :=
  (PinDrift.Internal.Run.effective_floor_pair tail early fulu i inside 0 0 capHigh 0 0 0).2.2.1 ceil
    alignedHigh startCap balanceCeil capCeil

end PinKeyFloor

end

section

/-! ## The penalty rate of one key in a rewards pass -/

namespace PinKeyFloor

open Base Uint64 Models

variable {preset : Preset} {config : Config}

/-- One rewards pass debits a key at a state at a rate of at most the pin reserve's leak rate.

The rate is taken at the key's effective balance at the state.

`pulledTotal` is R's total read.

The `quarter` is a quarter of it from 18 increments, and a fifth of an increment below.

The reserve reads the base reward per increment at the quarter.

The state's total is at least two thirds of R's, so its square root is at least the quarter's.

The score bound `scoreBound` covers the pass's score after its update.

That score is the score plus one bias.

Effective balances are whole increments.

`roomy` makes the rounding of the per-increment reward lose less than its fraction.

The flag term is `40 / 64` of a base reward per increment for each increment.

It fits in `2 * (increments * perIncrement)`.

The floor of a quotient that is at least one is at least half of it. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.passPenaltyRate_le_leak (z :
  ForkedBeaconState preset) (v : ℕ) (pulledTotal : ℕ)
    (scoreBound : ℕ) (facts : PinPresetFacts preset)
    (pulledFits : pulledTotal < 2 ^ 64)
    (aligned : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ effectiveAt z v)
    (band : 2 * pulledTotal ≤ 3 * activeBalanceTotal z.state)
    (scored : (if altair : .altair ≤ z.fork then
        (((z.state.inactivityScores altair).data[v]?).map (·.toNat)).getD 0 else 0) +
      config.INACTIVITY_SCORE_BIAS.toNat ≤ scoreBound) :
    let inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    let quarter := if 18 * inc ≤ pulledTotal then pulledTotal / 4 else inc / 5
    let perIncrement := inc * preset.BASE_REWARD_FACTOR.toNat / quarter.sqrt
    PinDrift.Internal.passPenaltyRate config z v ≤
      2 * (effectiveAt z v / inc * perIncrement) +
        effectiveAt z v * scoreBound /
          (config.INACTIVITY_SCORE_BIAS.toNat *
            (parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat) := by
  intro inc quarter perIncrement
  unfold PinDrift.Internal.passPenaltyRate
  let total := activeBalanceTotal z.state
  let score := if altair : .altair ≤ z.fork then
    (((z.state.inactivityScores altair).data[v]?).map (·.toNat)).getD 0 else 0
  have sizeInc : 10 ^ 8 ≤ inc := facts.incrementSize
  have roomy := Nat.le_trans (show 2 ^ 33 ≤ 2 ^ 35 by decide) facts.rewardScale
  have positive : 0 < inc := by omega
  have weights : TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat = 40 := by decide
  have denominator : WEIGHT_DENOMINATOR.toNat = 64 := by decide
  rw [weights, denominator]
  obtain ⟨k, hk⟩ := aligned
  have hinc : inc ≤ total := le_max_left _ _
  -- the numerator of the per-increment reward, `X`, dominates the square root of the quarter
  obtain ⟨X, hX⟩ : ∃ X, inc * preset.BASE_REWARD_FACTOR.toNat = X := ⟨_, rfl⟩
  rw [hX] at roomy
  have hp : perIncrement = X / quarter.sqrt := by
    simp only [perIncrement, hX]
  have incX : inc ≤ X := by
    rw [← hX]
    exact Nat.le_mul_of_pos_right _ (PinDrift.Internal.PinPresetFacts.reward facts)
  have quarterLe : quarter ≤ X ^ 2 := by
    by_cases big : 18 * inc ≤ pulledTotal
    · have : 2 ^ 66 ≤ X ^ 2 := by
        calc 2 ^ 66 = (2 ^ 33) ^ 2 := by norm_num
          _ ≤ X ^ 2 := Nat.pow_le_pow_left roomy 2
      have : pulledTotal / 4 < 2 ^ 62 := by omega
      simp only [quarter, big, ↓reduceIte]
      omega
    · simp only [quarter, big, ↓reduceIte]
      exact Nat.le_trans (Nat.div_le_self _ _)
        (Nat.le_trans incX (Nat.le_self_pow (by decide) _))
  have quarterTotal : quarter ≤ total := by
    by_cases big : 18 * inc ≤ pulledTotal
    · simp only [quarter, big, ↓reduceIte]
      have : 2 * pulledTotal ≤ 3 * total := band
      omega
    · simp only [quarter, big, ↓reduceIte]
      exact Nat.le_trans (Nat.div_le_self _ _) hinc
  have quarterPositive : 0 < quarter.sqrt := by
    refine Nat.sqrt_pos.mpr ?_
    by_cases big : 18 * inc ≤ pulledTotal
    · simp only [quarter, big, ↓reduceIte]
      omega
    · simp only [quarter, big, ↓reduceIte]
      omega
  have quarterRoot : quarter.sqrt ≤ X := by
    have := Nat.sqrt_le_sqrt quarterLe
    rwa [Nat.sqrt_eq'] at this
  have totalRoot : quarter.sqrt ≤ total.sqrt := Nat.sqrt_le_sqrt quarterTotal
  have perOne : 1 ≤ X / quarter.sqrt := (Nat.le_div_iff_mul_le quarterPositive).mpr (by omega)
  have rewardRate : 40 * preset.BASE_REWARD_FACTOR.toNat * effectiveAt z v / (64 * total.sqrt) ≤
      2 * (effectiveAt z v / inc * perIncrement) := by
    have increments : effectiveAt z v / inc = k := by
      rw [hk, Nat.mul_div_cancel_left _ positive]
    have numerator : 40 * preset.BASE_REWARD_FACTOR.toNat * effectiveAt z v = 40 * (k * X) := by
      rw [hk, ← hX]
      ring
    have totalPositive : 0 < total.sqrt := Nat.lt_of_lt_of_le quarterPositive totalRoot
    rw [increments, numerator]
    calc 40 * (k * X) / (64 * total.sqrt)
        ≤ 40 * (k * X) / (40 * total.sqrt) :=
          Nat.div_le_div_left (Nat.mul_le_mul_right _ (by decide)) (by positivity)
      _ = k * X / total.sqrt := Nat.mul_div_mul_left _ _ (by decide)
      _ ≤ k * X / quarter.sqrt := Nat.div_le_div_left totalRoot quarterPositive
      _ ≤ 2 * (k * perIncrement) := by
        refine Nat.div_le_of_le_mul ?_
        have split : X < (X / quarter.sqrt + 1) * quarter.sqrt := by
          have := Nat.lt_mul_div_succ X quarterPositive
          rwa [Nat.mul_comm] at this
        have step : X ≤ 2 * perIncrement * quarter.sqrt := by
          have : (X / quarter.sqrt + 1) ≤ 2 * (X / quarter.sqrt) := by omega
          rw [hp]
          exact Nat.le_of_lt (Nat.lt_of_lt_of_le split (Nat.mul_le_mul_right _ this))
        calc k * X ≤ k * (2 * perIncrement * quarter.sqrt) := Nat.mul_le_mul_left _ step
          _ = quarter.sqrt * (2 * (k * perIncrement)) := by ring
  have scoreRate : effectiveAt z v * (score + config.INACTIVITY_SCORE_BIAS.toNat) /
        (config.INACTIVITY_SCORE_BIAS.toNat *
          (parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat) ≤
      effectiveAt z v * scoreBound /
        (config.INACTIVITY_SCORE_BIAS.toNat *
          (parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat) :=
    Nat.div_le_div_right (Nat.mul_le_mul_left _ scored)
  exact Nat.add_le_add rewardRate scoreRate

end PinKeyFloor

/-! ## PinEventsKept -/

namespace PinEventsKept

open Base Uint64 Models DirectSafety

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- What a chain of steps keeps of the registry, at any forks.

Assigned exits stay, and a slash stays.

The withdrawable epoch of a key with an exit set only rises, and only for a slashed key. -/
structure _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Kept {f g : Fork} (s :
  BeaconState preset f) (t : BeaconState preset g) :
    Prop where
  life : RegistryLifecycle s t
  slashed : SlashedPersistence s t
  withdrawable : WithdrawableKept s t

/-- Two steps keep what one keeps.

The exit of the first comes from its lifecycle, and the slash of the second from its persistence. -/
private theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Kept.trans {f g h : Fork}
  {s : BeaconState preset f} {t : BeaconState preset g}
    {u : BeaconState preset h} (one : PinDrift.Internal.Kept s t) (two : PinDrift.Internal.Kept t u)
      : PinDrift.Internal.Kept s u where
  life := one.life.trans two.life
  slashed := one.slashed.trans two.slashed
  withdrawable i v w found read far := by
    obtain ⟨m, mFound, step⟩ := one.life.validators i v found
    have mFar : m.exitEpoch ≠ FAR_FUTURE_EPOCH := by rw [step.exitEpoch far]; exact far
    obtain ⟨le1, moved1⟩ := one.withdrawable i v m found mFound far
    obtain ⟨le2, moved2⟩ := two.withdrawable i m w mFound read mFar
    refine ⟨UInt64.le_trans le1 le2, ?_⟩
    rcases moved2 with flag | same
    · exact .inl flag
    · rcases moved1 with flag | same1
      · obtain ⟨w', read', marked⟩ := two.slashed i m mFound flag
        rw [read, Option.some.injEq] at read'
        subst read'
        exact .inl marked
      · exact .inr (same.trans same1)

/-- A state with the same validators keeps everything. -/
private theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Kept.of_data {f g : Fork}
  {s : BeaconState preset f} {t : BeaconState preset g}
    (same : t.validators.data = s.validators.data) : PinDrift.Internal.Kept s t where
  life := .of_data same
  slashed := .of_data same
  withdrawable i v w found read _ := by
    rw [same, found, Option.some.injEq] at read
    subst read
    exact ⟨UInt64.le_refl _, .inr rfl⟩

/-- A step that keeps the lifecycle, the slashes and each withdrawable epoch keeps everything. -/
private theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Kept.of_withdrawable {f g :
  Fork} {s : BeaconState preset f}
    {t : BeaconState preset g} (life : RegistryLifecycle s t) (slashed : SlashedPersistence s t)
    (same : ∀ (i : ℕ) (v : Validator), s.validators.data[i]? = some v →
      ∃ w, t.validators.data[i]? = some w ∧ w.withdrawableEpoch = v.withdrawableEpoch) :
    PinDrift.Internal.Kept s t where
  life := life
  slashed := slashed
  withdrawable i v w found read _ := by
    obtain ⟨w', read', equal⟩ := same i v found
    rw [read, Option.some.injEq] at read'
    subst read'
    exact ⟨UInt64.le_of_eq equal.symm, .inr equal⟩

/-- The pending deposits keep every validator of the registry before them as it was. -/
private theorem pendingDeposits_entries {fork : Fork} {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} (ok : processPendingDeposits config checks s electra = .ok t)
    (i : ℕ) (v : Validator) (found : s.validators.data[i]? = some v) :
    t.validators.data[i]? = some v := by
  obtain ⟨_, _, applied, _, next, _, _, _, _, _, _, _, _, appliedOk, rfl⟩ :=
    processPendingDeposits_applied ok
  have kept := foldlM_ok_invariant
    (fun u : BeaconState preset fork => u.validators.data[i]? = some v)
    (fun u deposit u' previous step => by
      rcases applyPendingDeposit_cases step with rfl | ⟨index, raised⟩ | ⟨_, added⟩
      · exact previous
      · rw [increaseBalance_validators raised]
        exact previous
      · have inside := (Array.getElem?_eq_some_iff.mp previous).1
        rw [addValidatorToRegistry_validators_eq_push added, Array.getElem?_push]
        simp only [Nat.ne_of_lt inside, ↓reduceIte]
        exact previous)
    found appliedOk
  exact kept

/-- The update of the effective balances keeps the withdrawable epoch of each validator. -/
private theorem effectiveUpdates_withdrawable {fork : Fork} {s t : BeaconState preset fork}
    (ok : processEffectiveBalanceUpdates s = .ok t) (i : ℕ) (v : Validator)
    (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧ w.withdrawableEpoch = v.withdrawableEpoch := by
  unfold processEffectiveBalanceUpdates at ok
  refine foldlM_ok_invariant (fun u : BeaconState preset fork =>
    ∃ w, u.validators.data[i]? = some w ∧ w.withdrawableEpoch = v.withdrawableEpoch)
    (fun u j u' previous step => ?_) ⟨v, found, rfl⟩ ok
  obtain ⟨w, read, equal⟩ := previous
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at step
  obtain ⟨validator, validatorOk, balance, _, next, _, set⟩ := step
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  by_cases same : i = j
  · subst same
    rw [getValidatorAt_eq_ok_iff.mp validatorOk, Option.some.injEq] at read
    subst read
    exact ⟨{ validator with effectiveBalance := next },
      by simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set], equal⟩
  · refine ⟨w, ?_, equal⟩
    simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, Ne.symm same,
      same] using read

/-- From Electra, every stage of an epoch keeps the registry. -/
private theorem kept_stage {fork : Fork} {k : EpochStage} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (edge : EpochStage.Edge config checks k s t) : PinDrift.Internal.Kept
      s t := by
  cases k
  case registry =>
    simp only [EpochStage.Edge] at edge
    exact ⟨registryLifecycle_processRegistryUpdates edge,
      .of_frame (frame_processRegistryUpdates edge).toFrame,
      withdrawableKept_processRegistryUpdates electra edge⟩
  case pendingDeposits =>
    simp only [EpochStage.Edge, electra, ↓reduceDIte] at edge
    exact PinDrift.Internal.Kept.of_withdrawable (registryLifecycle_processPendingDeposits edge)
      (.of_frame (frame_processPendingDeposits edge).toFrame)
      fun i v found => ⟨v, pendingDeposits_entries edge i v found, rfl⟩
  case effectiveBalances =>
    simp only [EpochStage.Edge] at edge
    exact PinDrift.Internal.Kept.of_withdrawable (registryLifecycle_processEffectiveBalanceUpdates
      edge)
      (.of_frame (frame_processEffectiveBalanceUpdates edge).toFrame)
      (effectiveUpdates_withdrawable edge)
  all_goals exact PinDrift.Internal.Kept.of_data (congrArg (·.data) (edge.validators_eq ⟨nofun,
    nofun, nofun⟩))

/-- From Electra, a whole epoch transition keeps the registry. -/
private theorem kept_processEpoch {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (ok : processEpoch config checks s = .ok t) : PinDrift.Internal.Kept
      s t :=
  (processEpoch_trace ok).transport (fun a b => PinDrift.Internal.Kept a b) (fun _ =>
    PinDrift.Internal.Kept.of_data rfl)
    (fun one two => one.trans two)
    (fun _ _ _ _ computed => kept_stage electra (EpochStage.action_cases.mp computed))

/-- From Electra, a slot of a run keeps the registry. -/
private theorem kept_slot {u w : ForkedBeaconState preset} (electra : .pectra ≤ u.fork)
    (ok : advanceSlotAcross config checks u = .ok w) : PinDrift.Internal.Kept u.state w.state := by
  obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
  obtain ⟨_, cached, epoched, _, cachedOk, epochedOk, afterEq⟩ := advanceSlot_ok slotOk
  have cachedKept : PinDrift.Internal.Kept u.state cached := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact PinDrift.Internal.Kept.of_data rfl
  have epochKept : PinDrift.Internal.Kept cached epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact kept_processEpoch electra epochedOk
    · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
      exact epochedOk ▸ PinDrift.Internal.Kept.of_data rfl
  have advancedKept : PinDrift.Internal.Kept u.state advanced := by
    rw [afterEq]
    exact cachedKept.trans (epochKept.trans (PinDrift.Internal.Kept.of_data rfl))
  exact (processUpgrades_induction (forked := ⟨u.fork, advanced⟩)
    (property := fun z => .pectra ≤ z.fork ∧ PinDrift.Internal.Kept u.state z.state)
    (fun {_ post} held more => ⟨Nat.le_trans held.1 (Nat.le_of_lt post.property),
      held.2.trans (PinDrift.Internal.Kept.of_data (upgradeNext_validators_of_electra held.1
        more))⟩)
    ⟨electra, advancedKept⟩ upgrades).2

/-- From Fulu and before Gloas, a block keeps the registry. -/
private theorem kept_block {fork : Fork} {a t : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    {due : upgradeDue config ⟨fork, a⟩ = false}
    {ok : applySignedBlock config checks engine a signed true = .ok t}
    (fulu : .fusaka ≤ fork) (early : fork < .glamsterdam) (matched : BalancesMatch a) :
    PinDrift.Internal.Kept a t := by
  have processed := (applySignedBlock_ok ok).2.1
  have frame := frame_processBlock processed
  refine ⟨registryLifecycle_processBlock processed, .of_frame frame, ?_⟩
  exact Run.withdrawableKept_of_same_epoch (Run.nil.snoc (Step.block engine signed due ok)) early
    fulu (by simp only [getCurrentEpoch, frame.slot]) matched

/-- From Fulu and before Gloas, a run keeps the registry. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.kept_run {g x y : ForkedBeaconState
  preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (fulu : .fusaka ≤ x.fork) (tail : Run config checks x y) (early : y.fork < .glamsterdam) :
    PinDrift.Internal.Kept x.state y.state := by
  induction tail with
  | nil => exact PinDrift.Internal.Kept.of_data rfl
  | @snoc middle last pre step ih =>
    have earlyMiddle : middle.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have fuluMiddle : .fusaka ≤ middle.fork :=
      Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps)
    refine (ih earlyMiddle).trans ?_
    cases step with
    | slot ok =>
      exact kept_slot (Nat.le_trans (by decide) fuluMiddle) ok
    | block engine signed due ok =>
      exact kept_block (engine := engine) (signed := signed) (due := due) (ok := ok)
        fuluMiddle early
        (run_justified_separated (shared.append pre) genesis).1.balancesMatch

/-- A replay step keeps the registry and the slot, and records no deposit event. -/
private structure Grew {f : Fork} (p q : BalanceReplay preset f) : Prop where
  kept : PinDrift.Internal.Kept p.1 q.1
  slot : q.1.slot = p.1.slot
  size : q.1.validators.data.size = p.1.validators.data.size
  events : ∀ e ∈ q.2, e ∈ p.2 ∨ e.source ≠ .deposits

/-- A replay step that does nothing grows the replay. -/
private theorem Grew.refl {f : Fork} (p : BalanceReplay preset f) : Grew p p :=
  ⟨PinDrift.Internal.Kept.of_data rfl, rfl, rfl, fun _ member => .inl member⟩

/-- Two growing replay steps in a row grow the replay. -/
private theorem Grew.trans {f : Fork} {p q r : BalanceReplay preset f} (one : Grew p q)
    (two : Grew q r) : Grew p r where
  kept := one.kept.trans two.kept
  slot := two.slot.trans one.slot
  size := two.size.trans one.size
  events e member := by
    rcases two.events e member with old | other
    · exact one.events e old
    · exact .inr other

private theorem mem_or_source_of_append {source : BalanceSource}
    {pre post : List (BalanceEvent preset)} {added e : BalanceEvent preset}
    (events : post = pre ++ [added]) (same : added.source = source)
    (member : e ∈ post) : e ∈ pre ∨ e.source = source := by
  rw [events] at member
  rcases List.mem_append.mp member with old | added
  · exact .inl old
  · exact .inr ((congrArg BalanceEvent.source (List.mem_singleton.mp added)).trans same)

/-- A carried pass changes the state by its action and records nothing. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.carryBalance_cases {f : Fork}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    {p q : BalanceReplay preset f} (ok : carryBalance action p = .ok q) :
    action p.1 = .ok q.1 ∧ q.2 = p.2 := by
  simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨after, computed, rfl⟩ := ok
  exact ⟨computed, rfl⟩

/-- A replay of reward and penalty deltas keeps the registry and records no deposit. -/
private theorem replayDeltas_grew {f : Fork} {source : BalanceSource}
    {deltas : Array Gwei × Array Gwei} {p q : BalanceReplay preset f}
    (notDeposit : source ≠ .deposits) (ok : replayDeltas source deltas p = .ok q) : Grew p q := by
  unfold replayDeltas at ok
  refine foldlM_ok_invariant (fun r => Grew p r) (fun r i r' previous step => ?_) (Grew.refl p) ok
  refine previous.trans ?_
  simp only [bind_ok_iff] at step
  obtain ⟨index, _, raised, raisedOk, loweredOk⟩ := step
  obtain ⟨_, _, _, raisedAction, raisedEvents⟩ := recordBalance_single raisedOk
  obtain ⟨_, _, _, loweredAction, loweredEvents⟩ := recordBalance_single loweredOk
  have raisedAction := liftAccessor_ok.mp raisedAction
  have loweredAction := liftAccessor_ok.mp loweredAction
  have first : Grew r raised :=
    ⟨PinDrift.Internal.Kept.of_data (congrArg (·.data) (increaseBalance_validators raisedAction)),
      (frame_increaseBalance raisedAction).toFrame.slot,
      congrArg Array.size (congrArg (·.data) (increaseBalance_validators raisedAction)),
      fun e member => by
        rcases mem_or_source_of_append raisedEvents rfl member with old | new
        · exact .inl old
        · refine .inr ?_
          rw [new]
          exact (show BalanceSource.rewards ≠ .deposits by decide)⟩
  have second : Grew raised r' :=
    ⟨PinDrift.Internal.Kept.of_data (congrArg (·.data) (decreaseBalance_validators loweredAction)),
      (frame_decreaseBalance loweredAction).toFrame.slot,
      congrArg Array.size (congrArg (·.data) (decreaseBalance_validators loweredAction)),
      fun e member => by
        rcases mem_or_source_of_append loweredEvents rfl member with old | new
        · exact .inl old
        · exact .inr (by rw [new]; exact notDeposit)⟩
  exact first.trans second

/-- The replay of the rewards and penalties keeps the registry and records no deposit. -/
private theorem replayRewards_grew {f : Fork} {p q : BalanceReplay preset f}
    (ok : replayRewards (config := config) p = .ok q) : Grew p q := by
  unfold replayRewards at ok
  split at ok
  · simp only [pure, Except.pure, Except.ok.injEq] at ok
    subst ok
    exact Grew.refl _
  · simp only [bind_ok_iff] at ok
    obtain ⟨ordinary, _, inactivity, _, ok⟩ := ok
    split at ok
    · obtain ⟨middle, middleOk, lastOk⟩ := bind_ok_iff.mp ok
      have first : Grew p middle := foldlM_ok_invariant (fun r => Grew p r)
        (fun _ _ _ previous step => previous.trans (replayDeltas_grew (by decide) step))
        (Grew.refl p) middleOk
      exact first.trans (replayDeltas_grew (by decide) lastOk)
    · obtain ⟨_, _, ok⟩ := bind_ok_iff.mp ok
      obtain ⟨one, oneOk, ok⟩ := bind_ok_iff.mp ok
      obtain ⟨two, twoOk, lastOk⟩ := bind_ok_iff.mp ok
      have middle : Grew one two := foldlM_ok_invariant (fun r => Grew one r)
        (fun _ _ _ previous step => previous.trans (replayDeltas_grew (by decide) step))
        (Grew.refl one) twoOk
      exact ((replayDeltas_grew (by decide) oneOk).trans middle).trans
        (replayDeltas_grew (by decide) lastOk)

/-- From Electra, each stage of an epoch before the pending deposits keeps the registry. -/
private theorem replay_stage {f : Fork} (electra : .pectra ≤ f) {k : EpochStage}
    (member : k ∈ [EpochStage.justification, .inactivity, .rewards, .registry, .slashings,
      .eth1Reset]) {p q : BalanceReplay preset f}
    (ok : epochReplayAction (config := config) (checks := checks) k p = .ok q) : Grew p q := by
  have sizeOf : ∀ {k' : EpochStage} (e : EpochStage.Edge config checks k' p.1 q.1),
      (k' ≠ .registry ∧ k' ≠ .pendingDeposits ∧ k' ≠ .effectiveBalances) →
        q.1.validators.data.size = p.1.validators.data.size := fun e other =>
    congrArg Array.size (congrArg (·.data) (e.validators_eq other))
  have ofEdge (edge : EpochStage.Edge config checks k p.1 q.1) (same : q.2 = p.2)
      (size : q.1.validators.data.size = p.1.validators.data.size) : Grew p q :=
    ⟨kept_stage electra edge, edge.slot_eq, size, fun e member => .inl (same ▸ member)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [epochReplayAction] at ok
    obtain ⟨action, same⟩ := PinDrift.Internal.carryBalance_cases ok
    exact ofEdge action same (sizeOf (k' := .justification) action ⟨nofun, nofun, nofun⟩)
  · simp only [epochReplayAction] at ok
    split at ok
    · obtain ⟨action, same⟩ := PinDrift.Internal.carryBalance_cases ok
      rename_i h
      have edge : EpochStage.Edge config checks .inactivity p.1 q.1 := by
        simp only [EpochStage.Edge, h, ↓reduceDIte]; exact action
      exact ofEdge edge same (sizeOf edge ⟨nofun, nofun, nofun⟩)
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      subst ok
      exact Grew.refl _
  · simp only [epochReplayAction] at ok
    exact replayRewards_grew ok
  · simp only [epochReplayAction] at ok
    obtain ⟨action, same⟩ := PinDrift.Internal.carryBalance_cases ok
    exact ofEdge action same (sameSizes_processRegistryUpdates (config := config)
      (by simpa only [EpochStage.Edge] using action)).1
  · simp only [epochReplayAction] at ok
    obtain ⟨_, _, _, action, events⟩ := recordBalance_single ok
    have edge : EpochStage.Edge config checks .slashings p.1 q.1 := action
    exact ⟨kept_stage electra edge, edge.slot_eq, sizeOf edge ⟨nofun, nofun, nofun⟩,
      fun e member => by
        rcases mem_or_source_of_append events rfl member with old | new
        · exact .inl old
        · refine .inr ?_
          rw [new]
          exact (show BalanceSource.slashings ≠ .deposits by decide)⟩
  · simp only [epochReplayAction] at ok
    split at ok
    · obtain ⟨action, same⟩ := PinDrift.Internal.carryBalance_cases ok
      rename_i h
      have edge : EpochStage.Edge config checks .eth1Reset p.1 q.1 := by
        simp only [EpochStage.Edge, h, ↓reduceDIte]; exact action
      exact ofEdge edge same (sizeOf edge ⟨nofun, nofun, nofun⟩)
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      subst ok
      exact Grew.refl _

/-- A later state has the exit and withdrawable epochs of an earlier one at its indices. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.ExitsStay {f g : Fork} (s : BeaconState
  preset f) (t : BeaconState preset g) : Prop :=
  ∀ (i : ℕ) (v : Validator), s.validators.data[i]? = some v →
    ∃ w, t.validators.data[i]? = some w ∧ w.exitEpoch = v.exitEpoch ∧
      w.withdrawableEpoch = v.withdrawableEpoch

/-- Two states in a row that keep the exits and withdrawable epochs keep them together. -/
private theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.ExitsStay.trans {f g h :
  Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    {u : BeaconState preset h} (one : PinDrift.Internal.ExitsStay s t) (two :
      PinDrift.Internal.ExitsStay t u) : PinDrift.Internal.ExitsStay s u :=
  fun i v found => by
    obtain ⟨m, mFound, exit, wd⟩ := one i v found
    obtain ⟨w, wFound, exit', wd'⟩ := two i m mFound
    exact ⟨w, wFound, exit'.trans exit, wd'.trans wd⟩

/-- A state with the same validators has the same exits. -/
private theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.ExitsStay.of_data {f g :
  Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    (same : t.validators.data = s.validators.data) : PinDrift.Internal.ExitsStay s t :=
  fun i v found => ⟨v, by rw [same]; exact found, rfl, rfl⟩

/-- The state at the input of a slot step's pending deposits, for a deposit event of the step.

It keeps the registry of the step's start, at its epoch and with at most its size.

The step's end state has the exit and withdrawable epochs of that input.

A step with a deposit event ends in a later epoch. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Step.deposit_input {u w :
  ForkedBeaconState preset}
    (ok : advanceSlotAcross config checks u = .ok w) (fulu : .fusaka ≤ u.fork)
    (early : w.fork < .glamsterdam) {events : List (BalanceEvent preset)}
    (replayed : (Step.slot ok : Step config checks u w).balanceEvents = .ok events) :
    ∀ e ∈ events, e.source = .deposits →
      PinDrift.Internal.Kept u.state e.before.state ∧
      e.before.state.validators.data.size ≤ u.state.validators.data.size ∧
      getCurrentEpoch e.before.state = getCurrentEpoch u.state ∧
      PinDrift.Internal.ExitsStay e.before.state w.state ∧
      (getCurrentEpoch u.state).toNat < (getCurrentEpoch w.state).toNat := by
  intro e member source
  have electraU : .pectra ≤ u.fork := Nat.le_trans (by decide) fulu
  obtain ⟨advanced, cached, crossings, advanceOk, upgrades, cachedOk, crossingOk, branch⟩ :=
    Step.balanceEvents_slot ok early replayed
  have noCrossings : crossings = [] :=
    DirectSafety.Apriori.Internal.upgradeBalanceReplay_electra_nil
      (u := ⟨u.fork, advanced⟩) electraU crossingOk
  rcases branch with ⟨_, eventsEq⟩ | ⟨middle, updated, recorded, recordOk, updatedOk,
      validatorsEq, _, eventsEq, next, nextNat, nextSlot, nextMod, -⟩
  · rw [eventsEq, noCrossings] at member
    cases member
  rw [eventsEq, noCrossings, List.append_nil] at member
  have cachedKept : PinDrift.Internal.Kept u.state cached := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact PinDrift.Internal.Kept.of_data rfl
  have cachedSlot : cached.slot = u.state.slot := (frame_processSlot cachedOk).slot
  have trace := epochBalanceReplay_trace recordOk
  change EpochTrace _ ([EpochStage.justification, .inactivity, .rewards, .registry, .slashings,
    .eth1Reset] ++ [.pendingDeposits, .pendingConsolidations]) _ _ at trace
  obtain ⟨six, head, rest⟩ := EpochTrace.append_iff.mp trace
  have grew : Grew (cached, []) six := head.transport (fun p q => Grew p q) Grew.refl Grew.trans
    (fun _ member _ _ computed => replay_stage electraU member computed)
  cases rest with
  | cons first rest =>
    cases rest with
    | cons second rest =>
      cases rest
      simp only [epochReplayAction, electraU, ↓reduceDIte, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at first second
      obtain ⟨deposited, depositOk, rfl⟩ := first
      obtain ⟨consolidated, consolidatedOk, same⟩ := second
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      rcases List.mem_append.mp member with old | last
      · rcases List.mem_append.mp old with old | added
        · rcases grew.events e old with listed | other
          · cases listed
          · exact absurd source other
        · rw [List.mem_singleton.mp added]
          have cachedSize : cached.validators.data.size = u.state.validators.data.size := by
            obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
            rfl
          have same : getCurrentEpoch six.1 = getCurrentEpoch u.state := by
            simp only [getCurrentEpoch, grew.slot, cachedSlot]
          have deposits : PinDrift.Internal.ExitsStay six.1 deposited := fun i v found =>
            ⟨v, pendingDeposits_entries depositOk i v found, rfl, rfl⟩
          have consolidations : PinDrift.Internal.ExitsStay deposited consolidated :=
            PinDrift.Internal.ExitsStay.of_data (congrArg (·.data)
              (processPendingConsolidations_fields consolidatedOk).1)
          have updates : PinDrift.Internal.ExitsStay consolidated updated := fun i v found => by
            obtain ⟨balance, owned⟩ := processEffectiveBalanceUpdates_owned updatedOk found
            obtain ⟨_, read, -⟩ :=
              processEffectiveBalanceUpdates_effectiveBalance_eq updatedOk found owned
            exact ⟨_, read, rfl, rfl⟩
          have upgraded : PinDrift.Internal.ExitsStay updated w.state :=
            PinDrift.Internal.ExitsStay.of_data
            ((processUpgrades_validators_of_electra (s := ⟨u.fork, advanced⟩) electraU early
              upgrades).trans (congrArg (·.data) validatorsEq))
          have crossed : (getCurrentEpoch u.state).toNat < (getCurrentEpoch w.state).toNat := by
            rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat,
              (processUpgrades_slot upgrades).trans nextSlot,
              nextSlot_epoch_of_boundary nextNat nextMod]
            omega
          exact ⟨cachedKept.trans grew.kept, (grew.size.trans cachedSize).le, same,
            deposits.trans (consolidations.trans (updates.trans upgraded)), crossed⟩
      · rw [List.mem_singleton.mp last] at source
        cases source

/-- Every deposit event of a slot step of the run starts at a state that keeps the registry.

A slot step records a deposit event only for the pending deposits of its epoch pass.

So the event starts at the input of that pass.

That input is the state after the first six stages of the epoch.

They are justification, inactivity, rewards, registry updates, slashings and the eth1 reset.

The steps of the run before the slot keep the registry, and so does each of those stages.

Block deposits are not covered.

From Electra they credit no existing key.

The registry at the event's start has at most the size of the one at the slot step's start.

A slashed key at the slot step's start is slashed at the event's start, and their epochs agree. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Run.events_kept {g x y :
  ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (fulu : .fusaka ≤ x.fork) (early : y.fork < .glamsterdam)
    {u w : ForkedBeaconState preset} (ok : advanceSlotAcross config checks u = .ok w)
    (contained : tail.Contains (Step.slot ok))
    {events : List (BalanceEvent preset)}
    (replayed : (Step.slot ok : Step config checks u w).balanceEvents = .ok events) :
    ∀ e ∈ events, e.source = .deposits →
      RegistryLifecycle x.state e.before.state ∧
      WithdrawableKept x.state e.before.state ∧
      getCurrentEpoch e.before.state ≤ getCurrentEpoch y.state ∧
      e.before.state.validators.data.size ≤ u.state.validators.data.size ∧
      SlashedPersistence u.state e.before.state ∧
      getCurrentEpoch e.before.state = getCurrentEpoch u.state := by
  intro e member source
  obtain ⟨pre, post, rfl⟩ := Run.contains_split tail (Step.slot ok) contained
  have stepFork := (Step.slot ok : Step config checks u w).chainStep.fork_le
  have earlyW : w.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early
  have earlyU : u.fork < .glamsterdam := Nat.lt_of_le_of_lt stepFork earlyW
  have fuluU : .fusaka ≤ u.fork := Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps)
  have run : PinDrift.Internal.Kept x.state u.state := PinDrift.Internal.kept_run shared genesis
    fulu pre earlyU
  have epochLe : getCurrentEpoch u.state ≤ getCurrentEpoch y.state :=
    currentEpoch_le_of_chainSteps
      (Relation.ReflTransGen.head (Step.slot ok : Step config checks u w).chainStep
        post.chainSteps)
  obtain ⟨kept, size, same, -, -⟩ := PinDrift.Internal.Step.deposit_input ok fuluU earlyW replayed e
    member source
  have total := run.trans kept
  exact ⟨total.life, total.withdrawable, same ▸ epochLe, size, kept.slashed, same⟩

end PinEventsKept

end

section

/-! ## Credits to exiting keys along a run -/

namespace PinKeys

open Base Uint64 Models DirectSafety

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-! ## Deposits leave the balance of an exiting key alone -/

/-- Every exiting key of the first state keeps its balance in the second state. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.KeepsExiting {f g : Fork} (s :
  BeaconState preset f) (t : BeaconState preset g) :
    Prop :=
  ∀ (i : ℕ) (v : Validator), s.validators.data[i]? = some v → v.exitEpoch.toNat < 2 ^ 64 - 1 →
    (getCurrentEpoch s).toNat < v.withdrawableEpoch.toNat →
    t.balances.data[i]? = s.balances.data[i]?

/-- Every deposit event of the list leaves the balance of an exiting key alone. -/
private def Quiet (events : List (BalanceEvent preset)) : Prop :=
  ∀ e ∈ events, e.source = .deposits → PinDrift.Internal.KeepsExiting e.before.state e.after.state

/-- The event raises no balance of the registry. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Unconditional (e : BalanceEvent preset)
  : Prop :=
  ∀ i, actualBalanceAt e.after i ≤ actualBalanceAt e.before i

/-- The empty list of events is quiet. -/
private theorem quiet_nil : Quiet ([] : List (BalanceEvent preset)) := fun _ mem => by
  simp at mem

/-- A pass that records no event keeps the events quiet. -/
private theorem quiet_carry {f : Fork}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    {pre post : BalanceReplay preset f} (initial : Quiet pre.2)
    (ok : carryBalance action pre = .ok post) : Quiet post.2 := by
  rw [(PinDrift.Internal.carryBalance_cases ok).2]
  exact initial

/-- A recorded pass keeps the events quiet when its deposit action keeps exiting balances. -/
private theorem quiet_record {f : Fork} {source : BalanceSource}
    {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    {pre post : BalanceReplay preset f} (initial : Quiet pre.2)
    (keeps : source = .deposits → ∀ t, action pre.1 = .ok t → PinDrift.Internal.KeepsExiting pre.1
      t)
    (ok : recordBalance source limits action pre = .ok post) : Quiet post.2 := by
  obtain ⟨credit, debit, _, actionOk, events⟩ := recordBalance_single ok
  rw [events]
  intro e member sourceEq
  rcases List.mem_append.mp member with old | new
  · exact initial e old sourceEq
  · obtain rfl := List.mem_singleton.mp new
    exact keeps sourceEq _ actionOk

/-- A new validator with no balance never raises a balance. -/
private theorem addValidatorToRegistry_zero_balance {f : Fork} {s t : BeaconState preset f}
    (altair : .altair ≤ f) {pubkey : Cryptography.Bls.BLSPubkey} {credentials : Bytes32}
    (ok : addValidatorToRegistry s pubkey credentials 0 = .ok t) (i : ℕ) :
    ((t.balances.data[i]?).map (·.toNat)).getD 0 ≤
      ((s.balances.data[i]?).map (·.toNat)).getD 0 := by
  unfold addValidatorToRegistry at ok
  simp only [altair, ↓reduceDIte, addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, balancesOk, _, _, _, _, _, _, rfl⟩ := ok
  show ((_ : Option Gwei).map (·.toNat)).getD 0 ≤ _
  rw [setOrAppendList_getElem? balancesOk]
  split <;> simp

/-- From Electra, a block deposit raises no balance. -/
private theorem processDeposit_balance_le {f : Fork} {s t : BeaconState preset f}
    (electra : .pectra ≤ f) {before : f < .hegota} {dep : Deposit}
    (ok : processDeposit config checks before s dep = .ok t) (i : ℕ) :
    actualBalanceAt ⟨f, t⟩ i ≤ actualBalanceAt ⟨f, s⟩ i := by
  obtain ⟨-, -, next, -, applied⟩ := processDeposit_ok ok
  rcases applyDeposit_cases applied with rfl | ⟨_, middle, pending, rfl | added, rfl⟩ |
      ⟨early, _⟩
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · exact addValidatorToRegistry_zero_balance (Nat.le_trans (by decide) electra) added i
  · exact absurd (Nat.lt_of_lt_of_le early electra) (Nat.lt_irrefl _)

/-- A property of the events of a block replay that each recorded event keeps.

Every operation of a block records an event of its own source.

The deposits of the block are the only events of the source `.deposits`.

No operation of a block records the source `.consolidations`. -/
private theorem blockReplay_invariant {f : Fork} (electra : .pectra ≤ f) (early : f < .glamsterdam)
    (P : List (BalanceEvent preset) → Prop) (nil : P [])
    (ordinary : ∀ (l : List (BalanceEvent preset)) (e : BalanceEvent preset),
      e.source ≠ .deposits → e.source ≠ .consolidations → P l → P (l ++ [e]))
    (deposit : ∀ (l : List (BalanceEvent preset)) (s t : BeaconState preset f)
      (before : f < .hegota) (dep : Deposit) (credit debit : ℕ), P l →
      processDeposit config checks before s dep = .ok t →
      P (l ++ [⟨.deposits, ⟨f, s⟩, ⟨f, t⟩, credit, debit⟩]))
    (engine : ExecutionEngine preset f) (s : BeaconState preset f)
    (block : BeaconBlock preset f) {post : BalanceReplay preset f}
    (ok : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok post) : P post.2 := by
  have carry {pre post : BalanceReplay preset f}
      {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
      (initial : P pre.2) (ok : carryBalance action pre = .ok post) : P post.2 := by
    rw [(PinDrift.Internal.carryBalance_cases ok).2]
    exact initial
  have record {pre post : BalanceReplay preset f} {source : BalanceSource}
      {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
      {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
      (notDeposit : source ≠ .deposits) (notConsolidation : source ≠ .consolidations)
      (initial : P pre.2) (ok : recordBalance source limits action pre = .ok post) :
      P post.2 := by
    obtain ⟨credit, debit, -, -, events⟩ := recordBalance_single ok
    rw [events]
    exact ordinary _ _ notDeposit notConsolidation initial
  have altair : .altair ≤ f := Nat.le_trans (by decide) electra
  have bellatrix : .bellatrix ≤ f := Nat.le_trans (by decide) electra
  unfold blockBalanceReplay at ok
  obtain ⟨headed, headedOk, rest⟩ := bind_ok_iff.mp ok
  have headedQuiet := carry nil headedOk
  simp only [bellatrix, ↓reduceDIte] at rest
  obtain ⟨executed, executedOk, rest⟩ := bind_ok_iff.mp rest
  have executedQuiet := record (by decide : BalanceSource.withdrawals ≠ .deposits)
    (by decide) headedQuiet executedOk
  simp only [bind_ok_iff] at rest
  obtain ⟨randao, randaoOk, voted, votedOk, expected, _, _, _,
    proposed, proposedOk, attested, attestedOk, rewarded, rewardedOk, deposited, depositOk,
    exited, exitOk, changed, changedOk, rest⟩ := rest
  have randaoQuiet := carry executedQuiet randaoOk
  have votedQuiet := carry randaoQuiet votedOk
  have proposedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun _ _ _ h ok => record (by decide : BalanceSource.slashings ≠ .deposits) (by decide) h ok)
    votedQuiet proposedOk
  have attestedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun _ _ _ h ok => record (by decide : BalanceSource.slashings ≠ .deposits) (by decide) h ok)
    proposedQuiet attestedOk
  have rewardedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun _ _ _ h ok => record (by decide : BalanceSource.rewards ≠ .deposits) (by decide) h ok)
    attestedQuiet rewardedOk
  have depositedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun pre dep post h ok => by
      obtain ⟨credit, debit, _, actionOk, events⟩ := recordBalance_single ok
      rw [events]
      exact deposit _ _ _ _ _ _ _ h actionOk)
    rewardedQuiet depositOk
  have exitedQuiet := carry depositedQuiet exitOk
  have changedQuiet := carry exitedQuiet changedOk
  simp only [electra, ↓reduceDIte, bind_ok_iff] at rest
  obtain ⟨deposits, depositRequestOk, withdrawals, withdrawalOk,
    requested, consolidations, rest⟩ := rest
  have depositsQuiet := carry changedQuiet depositRequestOk
  have withdrawalsQuiet := carry depositsQuiet withdrawalOk
  have requestedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun _ _ _ h ok => record (by decide : BalanceSource.excess ≠ .deposits) (by decide) h ok)
    withdrawalsQuiet consolidations
  simp only [altair, ↓reduceDIte] at rest
  exact record (by decide : BalanceSource.sync ≠ .deposits) (by decide) requestedQuiet rest

/-- From Electra, the deposit events of a block replay raise no balance. -/
private theorem blockReplay_unconditional {f : Fork} (electra : .pectra ≤ f)
    (early : f < .glamsterdam)
    (engine : ExecutionEngine preset f) (s : BeaconState preset f)
    (block : BeaconBlock preset f) {post : BalanceReplay preset f}
    (ok : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok post) :
    ∀ e ∈ post.2, e.source = .deposits → PinDrift.Internal.Unconditional e :=
  blockReplay_invariant electra early (fun l => ∀ e ∈ l, e.source = .deposits →
    PinDrift.Internal.Unconditional e)
    (fun _ h => by simp at h)
    (fun l e notDeposit _ held e' member sourceEq => by
      rcases List.mem_append.mp member with old | new
      · exact held e' old sourceEq
      · exact absurd ((List.mem_singleton.mp new) ▸ sourceEq) notDeposit)
    (fun l s t _ dep credit debit held computed e' member sourceEq => by
      rcases List.mem_append.mp member with old | new
      · exact held e' old sourceEq
      · obtain rfl := List.mem_singleton.mp new
        exact fun i => processDeposit_balance_le electra computed i)
    engine s block ok

/-- No operation of a block records a consolidation event. -/
private theorem blockReplay_noConsolidations {f : Fork} (electra : .pectra ≤ f)
    (early : f < .glamsterdam) (engine : ExecutionEngine preset f) (s : BeaconState preset f)
    (block : BeaconBlock preset f) {post : BalanceReplay preset f}
    (ok : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok post) : ∀ e ∈ post.2, e.source ≠ .consolidations :=
  blockReplay_invariant electra early (fun l => ∀ e ∈ l, e.source ≠ .consolidations)
    (fun _ h => by simp at h)
    (fun l e _ notConsolidation held e' member => by
      rcases List.mem_append.mp member with old | new
      · exact held e' old
      · exact (List.mem_singleton.mp new) ▸ notConsolidation)
    (fun l s t _ dep credit debit held _ e' member => by
      rcases List.mem_append.mp member with old | new
      · exact held e' old
      · obtain rfl := List.mem_singleton.mp new
        exact fun eq => by cases eq)
    engine s block ok

/-- The deposit events of an epoch replay leave the balance of an exiting key alone.

The pending deposits of an epoch are the only deposit events of the replay. -/
private theorem epochReplay_quiet {f : Fork} {s : BeaconState preset f}
    {post : BalanceReplay preset f}
    (ok : epochBalanceReplay (config := config) (checks := checks) s = .ok post) :
    Quiet post.2 := by
  refine (epochBalanceReplay_trace ok).transport
    (fun a b : BalanceReplay preset f => Quiet a.2 → Quiet b.2)
    (fun _ => id) (fun one two held => two (one held)) ?_ quiet_nil
  intro k member pre after step held
  cases k <;> simp only [epochReplayAction] at step
  case justification | registry => exact quiet_carry held step
  case inactivity | eth1Reset =>
    split at step
    · exact quiet_carry held step
    · cases step; exact held
  case rewards =>
    exact replayRewards_induction (fun pre => Quiet pre.2)
      (fun prior ok => quiet_record prior (fun eq => by cases eq) ok)
      (fun penalty prior ok => quiet_record prior
        (fun eq => by rcases penalty with rfl | rfl <;> cases eq) ok) held step
  case slashings => exact quiet_record held (fun eq => by cases eq) step
  case pendingDeposits =>
    split at step
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
      obtain ⟨deposited, depositedOk, rfl⟩ := step
      intro e member sourceEq
      rcases List.mem_append.mp member with old | new
      · exact held e old sourceEq
      · obtain rfl := List.mem_singleton.mp new
        intro i v found exited withdrawable
        exact processPendingDeposits_exited_balance depositedOk found exited withdrawable
    · cases step; exact held
  case pendingConsolidations =>
    split at step
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
      obtain ⟨consolidated, consolidatedOk, rfl⟩ := step
      intro e member sourceEq
      rcases List.mem_append.mp member with old | new
      · exact held e old sourceEq
      · obtain rfl := List.mem_singleton.mp new
        cases sourceEq
    · cases step; exact held
  all_goals simp [EpochStage.prefixStages] at member

/-- The deposit events of a slot step leave the balance of an exiting key alone. -/
private theorem slot_quiet {x y : ForkedBeaconState preset}
    (ok : advanceSlotAcross config checks x = .ok y)
    (early : y.fork < .glamsterdam)
    {events : List (BalanceEvent preset)} (replayed : (Step.slot ok).balanceEvents = .ok events) :
    Quiet events := by
  obtain ⟨advanced, cached, crossings, -, -, -, crossingOk, split⟩ :=
    Step.balanceEvents_slot ok early replayed
  have crossed : Quiet crossings := fun e member sourceEq => by
    cases (upgradeBalanceReplay_crossing crossingOk e member).symm.trans sourceEq
  rcases split with ⟨-, rfl⟩ | ⟨middle, updated, recorded, recordOk, -, -, -, rfl, -⟩
  · exact crossed
  · intro e member sourceEq
    rcases List.mem_append.mp member with old | new
    · exact epochReplay_quiet recordOk e old sourceEq
    · exact crossed e new sourceEq

/-- A deposit event of a run raises no balance, or it is an epoch's deposit event of a slot step.

Then it leaves the balance of an exiting key alone. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Located {x y : ForkedBeaconState
  preset} (tail : Run config checks x y)
    (e : BalanceEvent preset) : Prop :=
  PinDrift.Internal.Unconditional e ∨ ∃ (u w : ForkedBeaconState preset)
    (ok : advanceSlotAcross config checks u = .ok w) (es : List (BalanceEvent preset)),
    tail.Contains (Step.slot ok) ∧ (Step.slot ok : Step config checks u w).balanceEvents = .ok es ∧
      e ∈ es ∧ PinDrift.Internal.KeepsExiting e.before.state e.after.state

/-- Locate each deposit event and each consolidation event of a run.

A deposit event raises no balance, or it is in the events of a slot step of the run.

A consolidation event is in the events of a slot step of the run, since no block records one. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.run_located {x y :
  ForkedBeaconState preset} (tail : Run config checks x y)
    (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    (∀ e ∈ events, e.source = .deposits → PinDrift.Internal.Located tail e) ∧
      (∀ e ∈ events, e.source = .consolidations →
        ∃ (u w : ForkedBeaconState preset) (ok : advanceSlotAcross config checks u = .ok w)
          (es : List (BalanceEvent preset)), tail.Contains (Step.slot ok) ∧
          (Step.slot ok : Step config checks u w).balanceEvents = .ok es ∧ e ∈ es) := by
  induction tail generalizing events with
  | nil =>
    cases replayed
    exact ⟨fun e member => by simp at member, fun e member => by simp at member⟩
  | @snoc middle last pre step ih =>
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    obtain ⟨priorLocated, priorSlot⟩ := ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early) priorOk
    have lift : ∀ e, PinDrift.Internal.Located pre e → PinDrift.Internal.Located (pre.snoc step) e
      := by
      rintro e (unconditional | ⟨u, w, ok, es, contains, replayedEs, member, keeps⟩)
      · exact .inl unconditional
      · exact .inr ⟨u, w, ok, es, .earlier contains step, replayedEs, member, keeps⟩
    have liftSlot : ∀ e, (∃ (u w : ForkedBeaconState preset)
        (ok : advanceSlotAcross config checks u = .ok w) (es : List (BalanceEvent preset)),
        pre.Contains (Step.slot ok) ∧
          (Step.slot ok : Step config checks u w).balanceEvents = .ok es ∧ e ∈ es) →
        ∃ (u w : ForkedBeaconState preset) (ok : advanceSlotAcross config checks u = .ok w)
          (es : List (BalanceEvent preset)), (pre.snoc step).Contains (Step.slot ok) ∧
          (Step.slot ok : Step config checks u w).balanceEvents = .ok es ∧ e ∈ es := by
      rintro e ⟨u, w, ok, es, contains, replayedEs, member⟩
      exact ⟨u, w, ok, es, .earlier contains step, replayedEs, member⟩
    by_cases selected : (getCurrentEpoch middle.state).toNat ≤ high + 1
    · simp only [selected, ↓reduceIte, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at rest
      obtain ⟨added, addedOk, rfl⟩ := rest
      have inFork : .pectra ≤ middle.fork :=
        Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
      refine ⟨fun e member sourceEq => ?_, fun e member sourceEq => ?_⟩
      · rcases List.mem_append.mp member with old | new
        · exact lift e (priorLocated e old sourceEq)
        · cases step with
          | block engine signed due ok =>
            exact .inl (blockReplay_unconditional inFork early engine _ _
              (Step.balanceEvents_block early addedOk) e new sourceEq)
          | slot ok =>
            exact .inr ⟨_, _, ok, added, .last pre _, addedOk, new,
              slot_quiet ok early addedOk e new sourceEq⟩
      · rcases List.mem_append.mp member with old | new
        · exact liftSlot e (priorSlot e old sourceEq)
        · cases step with
          | block engine signed due ok =>
            exact absurd sourceEq (blockReplay_noConsolidations inFork early engine _ _
              (Step.balanceEvents_block early addedOk) e new)
          | slot ok => exact ⟨_, _, ok, added, .last pre _, addedOk, new⟩
    · simp only [selected, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      exact ⟨fun e member sourceEq => lift e (priorLocated e member sourceEq),
        fun e member sourceEq => liftSlot e (priorSlot e member sourceEq)⟩

/-! ## Consolidation credits of one pass -/

/-- The stake that a pending consolidation can move at a pass: the source's effective balance.

It counts only a source that is unslashed and can withdraw by the next epoch.

A pass reads the other sources without moving anything. -/
private def sourceBound {f : Fork} (s : BeaconState preset f) (next : Epoch)
    (c : PendingConsolidation) : ℕ :=
  match s.validators.data[c.sourceIndex.toNat]? with
  | some v => if v.slashed = false ∧ v.withdrawableEpoch ≤ next then v.effectiveBalance.toNat else 0
  | none => 0

/-- The credits of the balances at some positions, from one state to another. -/
private def creditedAt {f : Fork} (T : Finset ℕ) (s t : BeaconState preset f) : ℕ :=
  ∑ j ∈ T, (actualBalanceAt ⟨f, t⟩ j - actualBalanceAt ⟨f, s⟩ j)

/-- The credits at some positions telescope along two steps. -/
private theorem creditedAt_trans {f : Fork} (T : Finset ℕ) {a b c : BeaconState preset f} :
    creditedAt T a c ≤ creditedAt T a b + creditedAt T b c := by
  unfold creditedAt
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => by omega

/-- One transfer of a pass credits at most the amount moved, and only at its target. -/
private theorem creditedAt_transfer {f : Fork} (T : Finset ℕ)
    {s lowered raised : BeaconState preset f} {source target : ValidatorIndex} {moved : Gwei}
    (lowerOk : decreaseBalance s source moved = .ok lowered)
    (raiseOk : increaseBalance lowered target moved = .ok raised) :
    creditedAt T s raised ≤ if target.toNat ∈ T then moved.toNat else 0 := by
  have sizes := (sameSizes_increaseBalance raiseOk).2.trans (sameSizes_decreaseBalance lowerOk).2
  unfold creditedAt
  have pointwise : ∀ j, actualBalanceAt ⟨f, raised⟩ j - actualBalanceAt ⟨f, s⟩ j ≤
      if target.toNat = j then moved.toNat else 0 := by
    intro j
    by_cases inside : j < s.balances.data.size
    · obtain ⟨balance, found⟩ : ∃ balance, s.balances.data[j]? = some balance :=
        ⟨_, Array.getElem?_eq_getElem inside⟩
      obtain ⟨down, downFound, downEq⟩ := balance_decreaseBalance lowerOk found
      obtain ⟨up, upFound, upEq⟩ := balance_increaseBalance raiseOk downFound
      simp only [actualBalanceAt, found, upFound, Option.map_some, Option.getD_some]
      split at downEq <;> split at upEq <;> split <;> omega
    · have missing : s.balances.data[j]? = Option.none := Array.getElem?_eq_none (by omega)
      have outside : raised.balances.data[j]? = Option.none := Array.getElem?_eq_none (by omega)
      simp [actualBalanceAt, missing, outside]
  calc ∑ j ∈ T, (actualBalanceAt ⟨f, raised⟩ j - actualBalanceAt ⟨f, s⟩ j)
      ≤ ∑ j ∈ T, if target.toNat = j then moved.toNat else 0 :=
        Finset.sum_le_sum fun j _ => pointwise j
    _ = if target.toNat ∈ T then moved.toNat else 0 := by rw [Finset.sum_ite_eq]

/-- A pass credits the targets in `T` at most the effective balances of the due sources it reads.

The sources are those of the entries whose target is in `T`.

It keeps the registry and the number of balances. -/
private theorem pass_credits_le_targets {f : Fork} (next : Epoch) (T : Finset ℕ) :
    ∀ (items : List PendingConsolidation) {s t : BeaconState preset f} {read : ℕ},
      passPendingConsolidations next s items = .ok (t, read) →
      t.validators = s.validators ∧ t.balances.data.size = s.balances.data.size ∧
        creditedAt T s t ≤
          (((items.take read).filter fun c => c.targetIndex.toNat ∈ T).map
            (sourceBound s next)).sum
  | [], s, t, read, computed => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at computed
    obtain ⟨rfl, rfl⟩ := computed
    refine ⟨rfl, rfl, ?_⟩
    simp [creditedAt, actualBalanceAt]
  | c :: rest, s, t, read, computed => by
    simp only [passPendingConsolidations, liftAccessor, bind_ok_iff, mapError_ok_iff] at computed
    obtain ⟨source, sourceRead, computed⟩ := computed
    have found := getValidator_eq_ok_iff.mp sourceRead
    have bound : sourceBound s next c = if source.slashed = false ∧ source.withdrawableEpoch ≤ next
        then source.effectiveBalance.toNat else 0 := by
      simp [sourceBound, found]
    by_cases slashed : source.slashed = true
    · simp only [slashed, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at computed
      obtain ⟨⟨state', read'⟩, passed, rfl, rfl⟩ := computed
      obtain ⟨validators, sizes, credits⟩ := pass_credits_le_targets next T rest passed
      refine ⟨validators, sizes, ?_⟩
      by_cases inT : c.targetIndex.toNat ∈ T <;>
        simpa [bound, slashed, List.take_succ_cons, List.filter_cons, inT] using credits
    · replace slashed : source.slashed = false := by simpa using slashed
      by_cases early : next < source.withdrawableEpoch
      · simp only [slashed, early, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
          Except.ok.injEq, Prod.mk.injEq] at computed
        obtain ⟨rfl, rfl⟩ := computed
        refine ⟨rfl, rfl, ?_⟩
        simp [creditedAt, actualBalanceAt]
      · simp only [slashed, early, Bool.false_eq_true, ↓reduceIte, bind_ok_iff,
          mapError_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
        obtain ⟨balance, balanceOk, lowered, loweredOk, raised, raisedOk,
          ⟨state', read'⟩, passed, rfl, rfl⟩ := computed
        obtain ⟨validators, sizes, credits⟩ := pass_credits_le_targets next T rest passed
        have sameValidators := (increaseBalance_validators raisedOk).trans
          (decreaseBalance_validators loweredOk)
        have step := creditedAt_transfer T loweredOk raisedOk
        have sizeStep := (sameSizes_increaseBalance raisedOk).2.trans
          (sameSizes_decreaseBalance loweredOk).2
        have moved : (min balance source.effectiveBalance).toNat ≤
            source.effectiveBalance.toNat := by
          rw [Uint64.toNat_min]; exact Nat.min_le_right _ _
        have restBound : (((rest.take read').filter fun c => c.targetIndex.toNat ∈ T).map
            (sourceBound raised next)) =
            (((rest.take read').filter fun c => c.targetIndex.toNat ∈ T).map
              (sourceBound s next)) := by
          congr 1
          funext d
          simp only [sourceBound, sameValidators]
        refine ⟨validators.trans sameValidators, sizes.trans sizeStep, ?_⟩
        have total := creditedAt_trans T (a := s) (b := raised) (c := state')
        rw [restBound] at credits
        have isDue : sourceBound s next c = source.effectiveBalance.toNat := by
          rw [bound]; simp [slashed, UInt64.not_lt.mp early]
        by_cases inT : c.targetIndex.toNat ∈ T
        · simp only [inT, ↓reduceIte] at step
          simp only [List.take_succ_cons, List.filter_cons, inT, decide_true, ↓reduceIte,
            List.map_cons, List.sum_cons, isDue]
          omega
        · simp only [inT, ↓reduceIte] at step
          simp only [List.take_succ_cons, List.filter_cons, inT, decide_false,
            Bool.false_eq_true, ↓reduceIte]
          omega

/-! ## The queue of a run from X, and the stake a pass can move -/

/-- From Electra on, the funding sources are the pending consolidations. -/
private theorem fundingSources_eq {f : Fork} (electra : .pectra ≤ f) (s : BeaconState preset f) :
    fundingSources s = (s.pendingConsolidations electra).data.toList := by
  simp [fundingSources, electra]

/-- The queue is the unread part of X's queue, then entries that are new since X.

Every new entry has a source whose exit was assigned after `e0`, the epoch of X. -/
private def Shape (L : List PendingConsolidation) (e0 : Epoch) (n : ℕ) {f : Fork}
    (z : BeaconState preset f) : Prop :=
  ∃ N : List PendingConsolidation, fundingSources z = L.drop n ++ N ∧
    ∀ c ∈ N, ∃ w, z.validators.data[c.sourceIndex.toNat]? = some w ∧
      e0 < w.exitEpoch ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH

/-- An assigned exit stays fixed, so its queue entry still has a source that exited after `e0`. -/
private theorem carry_source_exit {e0 : Epoch} {i : ℕ} {f g : Fork}
    {a : BeaconState preset f} {b : BeaconState preset g} (life : RegistryLifecycle a b)
    (source : ∃ w, a.validators.data[i]? = some w ∧
      e0 < w.exitEpoch ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    ∃ w, b.validators.data[i]? = some w ∧
      e0 < w.exitEpoch ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH := by
  obtain ⟨w, read, later, assigned⟩ := source
  obtain ⟨w', read', kept⟩ := life.validators i w read
  exact ⟨w', read', by rw [kept.exitEpoch assigned]; exact ⟨later, assigned⟩⟩

/-- A state of any fork with the same queue and a later life of its validators has the shape. -/
private theorem Shape.carry {L : List PendingConsolidation} {e0 : Epoch} {n : ℕ} {f g : Fork}
    {a : BeaconState preset f} {b : BeaconState preset g} (shape : Shape L e0 n a)
    (queue : fundingSources b = fundingSources a) (life : RegistryLifecycle a b) :
    Shape L e0 n b := by
  obtain ⟨N, eq, new⟩ := shape
  exact ⟨N, queue.trans eq, fun c member => carry_source_exit life (new c member)⟩

/-- A block that grows the queue keeps the shape. -/
private theorem Shape.grow {L : List PendingConsolidation} {e0 : Epoch} {n : ℕ} {f : Fork}
    {a b : BeaconState preset f} (electra : .pectra ≤ f) (shape : Shape L e0 n a)
    (grows : ConsolidationQueueRise.Appends a b) (life : RegistryLifecycle a b)
    (started : e0 ≤ getCurrentEpoch a) :
    Shape L e0 n b := by
  obtain ⟨N, eq, new⟩ := shape
  obtain ⟨added, queue, fresh⟩ := grows electra
  refine ⟨N ++ added, by rw [fundingSources_eq electra, queue, ← fundingSources_eq electra, eq,
    List.append_assoc], fun c member => ?_⟩
  rcases List.mem_append.mp member with old | recent
  · exact carry_source_exit life (new c old)
  · obtain ⟨w, read, later, assigned⟩ := fresh c recent
    exact ⟨w, read, UInt64.lt_of_le_of_lt started later, assigned⟩

/-- A pass that reads `r` entries moves the shape on by `r`. -/
private theorem Shape.pass {L : List PendingConsolidation} {e0 : Epoch} {n r : ℕ} {f : Fork}
    {a b : BeaconState preset f} (shape : Shape L e0 n a)
    (queue : fundingSources b = (fundingSources a).drop r) (life : RegistryLifecycle a b) :
    Shape L e0 (n + r) b := by
  obtain ⟨N, eq, new⟩ := shape
  refine ⟨N.drop (r - (L.length - n)), ?_, fun c member => ?_⟩
  · rw [queue, eq, List.drop_append, List.drop_drop]
    simp [List.length_drop]
  · exact carry_source_exit life (new c (List.mem_of_mem_drop member))

/-- The stake that X lets a pending consolidation move: the cap of its source at X.

It counts only a source that is unslashed at X and can withdraw by `high + 1`. -/
private def capBound (x : ForkedBeaconState preset) (high : ℕ) (c : PendingConsolidation) : ℕ :=
  match x.state.validators.data[c.sourceIndex.toNat]? with
  | some v =>
    if v.slashed = false ∧ v.withdrawableEpoch.toNat ≤ high + 1 then
      (withdrawalMaxEffectiveBalance preset x.fork v).toNat
    else 0
  | none => 0

/-- A key that cannot switch to compounding credentials has a cap that does not rise. -/
private theorem withdrawalMax_le {f g : Fork} (hf : .pectra ≤ f) (hg : .pectra ≤ g)
    (caps : CapOrder preset) {v w : Validator}
    (frozen : hasCompoundingWithdrawalCredential w = true →
      hasCompoundingWithdrawalCredential v = true) :
    withdrawalMaxEffectiveBalance preset f w ≤ withdrawalMaxEffectiveBalance preset g v := by
  simp only [withdrawalMaxEffectiveBalance, hf, hg, ↓reduceIte, getMaxEffectiveBalance]
  by_cases hw : hasCompoundingWithdrawalCredential w = true
  · simp [hw, frozen hw]
  · by_cases hv : hasCompoundingWithdrawalCredential v = true
    · simp only [hw, hv, Bool.false_eq_true, ↓reduceIte]
      exact caps.compounding
    · simp only [hw, hv, Bool.false_eq_true, ↓reduceIte]
      exact UInt64.le_refl _

/-- What a run from X, at a state `p` of the epoch pass, knows about the pending consolidations. -/
private structure PassFacts (x : ForkedBeaconState preset) (high : ℕ) {f : Fork}
    (p : BeaconState preset f) : Prop where
  electraX : .pectra ≤ x.fork
  electraP : .pectra ≤ f
  caps : CapOrder preset
  delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  within : high + 2 ≤ (getCurrentEpoch x.state).toNat +
    config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  life : RegistryLifecycle x.state p
  cap : Internal.CapStep config x.state p
  orderedX : PendingConsolidationsOrdered config (getCurrentEpoch x.state).toNat x.state
  invariantP : PendingConsolidationInvariant config p
  cappedX : ∀ v ∈ x.state.validators.data,
    v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset x.fork v
  next : (getCurrentEpoch p).toNat + 1 ≤ high + 1
  nextNat : (getCurrentEpoch p + 1).toNat = (getCurrentEpoch p).toNat + 1

/-- An entry of X's queue, still queued at the pass, moves at most its cap at X. -/
private theorem old_entry_bound {x : ForkedBeaconState preset} {high : ℕ} {f : Fork}
    {p : BeaconState preset f} (facts : PassFacts (config := config) x high p)
    {c : PendingConsolidation}
    (inX : c ∈ (x.state.pendingConsolidations facts.electraX).data.toList)
    (inP : c ∈ (p.pendingConsolidations facts.electraP).data.toList) :
    sourceBound p (getCurrentEpoch p + 1) c ≤ capBound x high c := by
  obtain ⟨v, foundX, -, -, assignedX⟩ := (facts.orderedX.1 facts.electraX).2 c inX
  obtain ⟨-, unslashedX, -⟩ := (facts.orderedX.2 facts.electraX).2 c inX v foundX
  obtain ⟨wP, foundP', -, exitDelayP, -⟩ := (facts.invariantP facts.electraP).2 c inP
  obtain ⟨w, foundP, lifecycle⟩ := facts.life.validators _ v foundX
  obtain rfl : w = wP := Option.some.inj (foundP.symm.trans foundP')
  simp only [sourceBound, capBound, foundP, foundX]
  split
  · rename_i due
    have exitEq := lifecycle.exitEpoch assignedX
    have slashedX : v.slashed = false := by
      cases flag : v.slashed
      · rfl
      · have := ((facts.cap.withdrawal _ v w foundX foundP).1 flag assignedX).1
        rw [due.1] at this
        cases this
    have dueNat := UInt64.le_iff_toNat_le.mp due.2
    have withdrawX := unslashedX slashedX
    rw [facts.nextNat] at dueNat
    have exitNat := congrArg UInt64.toNat exitEq
    have exitDelay : w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
        w.withdrawableEpoch.toNat := exitDelayP
    have dueX : v.slashed = false ∧ v.withdrawableEpoch.toNat ≤ high + 1 :=
      ⟨slashedX, by have := facts.next; omega⟩
    simp only [dueX, and_self, ↓reduceIte]
    have capped : w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f w :=
      facts.cap.capped facts.cappedX w (Array.mem_of_getElem? foundP)
    have bounded := withdrawalMax_le facts.electraP facts.electraX facts.caps
      ((facts.cap.frozen _ v w foundX foundP assignedX).2)
    exact UInt64.le_iff_toNat_le.mp (UInt64.le_trans capped bounded)
  · exact Nat.zero_le _

/-- An entry that is new since X moves nothing at the pass.

Its source exits after X, so it withdraws after the run. -/
private theorem new_entry_zero {x : ForkedBeaconState preset} {high : ℕ} {f : Fork}
    {p : BeaconState preset f} (facts : PassFacts (config := config) x high p)
    {c : PendingConsolidation}
    (inP : c ∈ (p.pendingConsolidations facts.electraP).data.toList) {w : Validator}
    (foundW : p.validators.data[c.sourceIndex.toNat]? = some w)
    (fresh : getCurrentEpoch x.state < w.exitEpoch) :
    sourceBound p (getCurrentEpoch p + 1) c = 0 := by
  obtain ⟨w', found', -, exitDelay, -⟩ := (facts.invariantP facts.electraP).2 c inP
  obtain rfl : w' = w := Option.some.inj (found'.symm.trans foundW)
  have later := UInt64.lt_iff_toNat_lt.mp fresh
  simp only [sourceBound, foundW]
  split
  · rename_i due
    have dueNat := UInt64.le_iff_toNat_le.mp due.2
    rw [facts.nextNat] at dueNat
    have := facts.next
    have := facts.within
    have := facts.delay
    omega
  · rfl

/-- A pass, from a state with the shape, credits the targets in `T` at most the caps at X.

The caps are those of the entries it reads whose target is in `T`. -/
private theorem pass_step_targets {x : ForkedBeaconState preset} {high : ℕ} {f : Fork}
    {p t : BeaconState preset f} {n : ℕ} (facts : PassFacts (config := config) x high p)
    (shape : Shape (x.state.pendingConsolidations facts.electraX).data.toList
      (getCurrentEpoch x.state) n p)
    (computed : processPendingConsolidations p facts.electraP = .ok t) :
    ∃ r, Shape (x.state.pendingConsolidations facts.electraX).data.toList
        (getCurrentEpoch x.state) (n + r) t ∧ RegistryLifecycle p t ∧
      ∀ T : Finset ℕ, creditedAt T p t ≤
        (((((x.state.pendingConsolidations facts.electraX).data.toList.drop n).take r).filter
          fun c => c.targetIndex.toNat ∈ T).map (capBound x high)).sum := by
  obtain ⟨result, passed, balancesEq, queueEq⟩ := processPendingConsolidations_pass computed
  have sameValidators := (processPendingConsolidations_kept computed).1
  have life : RegistryLifecycle p t := .of_data (congrArg (·.data) sameValidators)
  have queue : fundingSources t = (fundingSources p).drop result.2 := by
    rw [fundingSources_eq facts.electraP, fundingSources_eq facts.electraP]
    exact queueEq
  refine ⟨result.2, shape.pass queue life, life, fun T => ?_⟩
  obtain ⟨validators, sizes, credits⟩ :=
    pass_credits_le_targets (getCurrentEpoch p + 1) T _ passed
  have creditsEq : creditedAt T p t = creditedAt T p result.1 := by
    simp [creditedAt, actualBalanceAt, balancesEq]
  rw [creditsEq]
  refine Nat.le_trans credits ?_
  obtain ⟨N, eq, new⟩ := shape
  rw [← fundingSources_eq facts.electraP, eq, List.take_append, List.filter_append,
    List.map_append, List.sum_append]
  have oldPart : (((((x.state.pendingConsolidations facts.electraX).data.toList.drop n).take
      result.2).filter fun c => c.targetIndex.toNat ∈ T).map
        (sourceBound p (getCurrentEpoch p + 1))).sum ≤
      (((((x.state.pendingConsolidations facts.electraX).data.toList.drop n).take
        result.2).filter fun c => c.targetIndex.toNat ∈ T).map (capBound x high)).sum := by
    apply List.sum_le_sum
    intro c member
    have inDrop := List.mem_of_mem_take (List.mem_of_mem_filter member)
    refine old_entry_bound facts (List.mem_of_mem_drop inDrop) ?_
    rw [← fundingSources_eq facts.electraP, eq]
    exact List.mem_append_left _ inDrop
  have newPart : (((N.take (result.2 -
      ((x.state.pendingConsolidations facts.electraX).data.toList.drop n).length)).filter
        fun c => c.targetIndex.toNat ∈ T).map
        (sourceBound p (getCurrentEpoch p + 1))).sum = 0 := by
    apply List.sum_eq_zero
    intro m member
    obtain ⟨c, inTake, rfl⟩ := List.mem_map.mp member
    have inN := List.mem_of_mem_take (List.mem_of_mem_filter inTake)
    obtain ⟨w, foundW, fresh, -⟩ := new c inN
    refine new_entry_zero facts ?_ foundW fresh
    rw [← fundingSources_eq facts.electraP, eq]
    exact List.mem_append_right _ inN
  omega

/-- The upgrades due at a slot keep the shape of the queue. -/
private theorem upgrade_shape {L : List PendingConsolidation} {e0 : Epoch} {n : ℕ}
    {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (electra : .pectra ≤ pre.fork) (shape : Shape L e0 n pre.state)
    (ok : upgradeNext config checks pre = .ok post) (early : post.val.fork < .glamsterdam) :
    .pectra ≤ post.val.fork ∧ Shape L e0 n post.val.state := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · exact absurd electra (Nat.not_le_of_lt (by decide : Fork.phase0 < Fork.pectra))
  · exact absurd electra (Nat.not_le_of_lt (by decide : Fork.altair < Fork.pectra))
  · exact absurd electra (Nat.not_le_of_lt (by decide : Fork.bellatrix < Fork.pectra))
  · exact absurd electra (Nat.not_le_of_lt (by decide : Fork.shapella < Fork.pectra))
  · exact absurd electra (Nat.not_le_of_lt (by decide : Fork.dencun < Fork.pectra))
  · obtain ⟨_, upgraded, rfl⟩ := ok
    refine ⟨(by decide : Fork.pectra ≤ Fork.fusaka),
      shape.carry ?_ (.of_data (upgradeToFulu_spec upgraded).1)⟩
    simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
    obtain ⟨_, -, rfl⟩ := upgraded
    simp [fundingSources, carryFields, carryList, carryRooted,
      show Fork.pectra ≤ Fork.fusaka from by decide]
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.lt_irrefl _ early)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.not_le_of_lt early (show Fork.glamsterdam ≤ .hegota from by decide))

/-- All the upgrades of a step keep the shape of the queue, as each one does. -/
private theorem upgrades_shape {L : List PendingConsolidation} {e0 : Epoch} {n : ℕ}
    {advanced last : ForkedBeaconState preset} (electra : .pectra ≤ advanced.fork)
    (early : last.fork < .glamsterdam) (shape : Shape L e0 n advanced.state)
    (ok : processUpgrades config checks advanced = .ok last) : Shape L e0 n last.state := by
  have rest := processUpgrades_induction
    (property := fun z => z.fork < .glamsterdam → .pectra ≤ z.fork ∧ Shape L e0 n z.state)
    (fun {pre post} h ok early => by
      obtain ⟨electraPre, shapePre⟩ := h (Nat.lt_trans post.property early)
      exact upgrade_shape electraPre shapePre ok early)
    (fun _ => ⟨electra, shape⟩) ok
  exact (rest early).2

/-! ## The stages of an epoch -/

/-- The order of the pending consolidations of a state at its own epoch. -/
private abbrev OrderedAt {f : Fork} (config : Config) (s : BeaconState preset f) : Prop :=
  PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s

/-- A stage other than the pass keeps the slot, the queue and the order, and the lifecycle. -/
private theorem stage_rel {f : Fork} (electra : .pectra ≤ f) {k : EpochStage}
    (notPass : k ≠ .pendingConsolidations) {a b : BeaconState preset f}
    (edge : EpochStage.Edge config checks k a b) :
    RegistryLifecycle a b ∧ b.slot = a.slot ∧ fundingSources b = fundingSources a ∧
      (OrderedAt config a → OrderedAt config b) := by
  refine ⟨edge.registryLifecycle, edge.slot_eq, ?_, edge.pendingConsolidationsOrdered⟩
  rw [fundingSources_eq electra, fundingSources_eq electra,
    show b.pendingConsolidations = a.pendingConsolidations from edge.samePendingQueue notPass]

/-- The stages before the pass, from the cached state, keep what the pass reads. -/
private theorem prefix_rel {f : Fork} (electra : .pectra ≤ f) {stages : List EpochStage}
    (notPass : ∀ k ∈ stages, k ≠ .pendingConsolidations) {a b : BeaconState preset f}
    (trace : EpochTrace (EpochStage.action config checks) stages a b) :
    RegistryLifecycle a b ∧ b.slot = a.slot ∧ fundingSources b = fundingSources a ∧
      (OrderedAt config a → OrderedAt config b) := by
  apply trace.transport
    (fun a b : BeaconState preset f => RegistryLifecycle a b ∧ b.slot = a.slot ∧
      fundingSources b = fundingSources a ∧ (OrderedAt config a → OrderedAt config b))
    (fun _ => ⟨.refl _, rfl, rfl, id⟩)
    (fun one two => ⟨one.1.trans two.1, two.2.1.trans one.2.1, two.2.2.1.trans one.2.2.1,
      two.2.2.2 ∘ one.2.2.2⟩)
  intro k member s t computed
  exact stage_rel electra (notPass k member) (EpochStage.action_cases.mp computed)

/-- The events that the replay of the rewards records are rewards, penalties or inactivity. -/
private theorem rewards_noConsolidations {f : Fork} {pre post : BalanceReplay preset f}
    (initial : ∀ e ∈ pre.2, e.source ≠ .consolidations)
    (ok : replayRewards (config := config) pre = .ok post) :
    ∀ e ∈ post.2, e.source ≠ .consolidations := by
  have record {pre post : BalanceReplay preset f} {source : BalanceSource}
      {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
      {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
      (notConsolidation : source ≠ .consolidations)
      (initial : ∀ e ∈ pre.2, e.source ≠ .consolidations)
      (ok : recordBalance source limits action pre = .ok post) :
      ∀ e ∈ post.2, e.source ≠ .consolidations := fun e member => by
    obtain ⟨_, _, _, _, events⟩ := recordBalance_single ok
    rcases PinEventsKept.mem_or_source_of_append events rfl member with old | new
    · exact initial e old
    · exact new ▸ notConsolidation
  exact replayRewards_induction (fun pre => ∀ e ∈ pre.2, e.source ≠ .consolidations)
    (fun prior ok => record (by decide) prior ok)
    (fun penalty prior ok => record (by rcases penalty with rfl | rfl <;> decide) prior ok)
    initial ok

/-- The queue of X. -/
private abbrev queueX (x : ForkedBeaconState preset) (h : .pectra ≤ x.fork) :
    List PendingConsolidation :=
  (x.state.pendingConsolidations h).data.toList

/-- A slot step moves the shape of the queue on.

It credits the targets in `T` at most the caps of the entries it reads that have such a target. -/
private theorem slot_step_targets {g x m last : ForkedBeaconState preset}
    (shared : Run config checks g x) (pre : Run config checks x m)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) (electra : .pectra ≤ x.fork)
    (high : ℕ) (within : high + 2 ≤ (getCurrentEpoch x.state).toNat +
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : advanceSlotAcross config checks m = .ok last) (early : last.fork < .glamsterdam)
    (endEpoch : (getCurrentEpoch last.state).toNat ≤ high + 1) {n : ℕ}
    (shape : Shape (queueX x electra) (getCurrentEpoch x.state) n m.state) :
    ∃ r, Shape (queueX x electra) (getCurrentEpoch x.state) (n + r) last.state ∧
      ∀ {events : List (BalanceEvent preset)},
        (Step.slot ok : Step config checks m last).balanceEvents = .ok events →
        ∀ T : Finset ℕ,
          (T.sum fun i => ((events.filter (·.source = .consolidations)).map
            (PinDrift.Internal.keyCredit i)).sum) ≤
            (((((queueX x electra).drop n).take r).filter fun c => c.targetIndex.toNat ∈ T).map
              (capBound x high)).sum := by
  have beforeFork : m.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Step.slot ok).chainStep.fork_le early
  have mFork : .pectra ≤ m.fork := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
  obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
  obtain ⟨crossings, crossingOk, -⟩ := upgradeBalanceReplay_bounded upgrades
  have advanceCopy := slotOk
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at advanceCopy
  obtain ⟨next, nextOk, cached, cachedOk, epoched, epochOk, afterEq⟩ := advanceCopy
  have sum : next.toNat = m.state.slot.toNat + 1 :=
    (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp (liftAccessor_ok.mp nextOk))).2
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have shapeCached : Shape (queueX x electra) (getCurrentEpoch x.state) n cached := by
    rw [cachedEq]; exact shape
  by_cases boundary : next % preset.SLOTS_PER_EPOCH = 0
  · simp only [epochIfLast, boundary, ↓reduceIte] at epochOk
    obtain ⟨middle, updated, recorded, recordOk, updatedOk, validators, balances, cutOk⟩ :=
      epochBalanceReplay_result_before cached epoched beforeFork epochOk
    obtain ⟨justified, scored, rewarded, registered, slashed, reset, deposited, rewardEvents,
      limit, trace6, justifiedOk, scoredOk, rewardedOk, registeredOk, slashedOk, resetOk,
      depositedOk, consolidatedOk, rewardReplay, recordedEq⟩ := funding_epoch_site cutOk recordOk
    have trace7 : EpochTrace (EpochStage.action config checks)
        [.justification, .inactivity, .rewards, .registry, .slashings, .eth1Reset,
          .pendingDeposits] cached deposited :=
      EpochTrace.append_iff.mpr
        ⟨reset, trace6, .cons (EpochStage.action_cases.mpr depositedOk) .nil⟩
    simp only [EpochStage.Edge, mFork, ↓reduceDIte] at consolidatedOk
    simp only [mFork, ↓reduceDIte] at recordedEq
    -- The facts about the run before the step.
    have xEarly : x.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (fork_le_of_chainSteps pre.chainSteps) beforeFork
    have lifeXM : RegistryLifecycle x.state m.state := pre.registryLifecycle
    have capXM := (Internal.CapStep.run pre caps.activation caps.compounding beforeFork).1
    have orderedM : OrderedAt config m.state :=
      (shared.append pre).pendingConsolidationsOrdered genesis beforeFork delay
    have orderedX := shared.pendingConsolidationsOrdered genesis xEarly delay
    have cappedX := shared.effectiveBalance_capped genesis caps.activation caps.compounding xEarly
    -- The cached state is the state of the step, up to its roots.
    have lifeMC : RegistryLifecycle m.state cached := .of_data (by rw [cachedEq])
    have slotMC : cached.slot = m.state.slot := by rw [cachedEq]
    have queueMC : fundingSources cached = fundingSources m.state := by rw [cachedEq]; rfl
    have orderedC : OrderedAt config cached := by rw [cachedEq]; exact orderedM
    have capMC : Internal.CapStep config m.state cached := by
      rw [cachedEq]; exact Internal.CapStep.data
    -- The stages up to the pass.
    obtain ⟨lifeCD, slotCD, queueCD, orderedCD⟩ := prefix_rel mFork (by
      intro k member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact fun h => by cases h)
      trace7
    have capCD := Internal.CapStep.epochTrace trace7
    have epochD : getCurrentEpoch deposited = getCurrentEpoch m.state := by
      simp only [getCurrentEpoch, slotCD, slotMC]
    -- The epoch of the next state.
    have epochLast : (getCurrentEpoch last.state).toNat = (getCurrentEpoch m.state).toNat + 1 := by
      have advancedEpoch : getCurrentEpoch last.state = getCurrentEpoch
          ({ epoched with slot := next } : BeaconState preset m.fork) := by
        rw [afterEq]
        exact congrArg (computeEpochAtSlot preset) (processUpgrades_slot upgrades)
      rw [advancedEpoch]
      have nextEpoch :=
        getCurrentEpoch_toNat ({ epoched with slot := next } : BeaconState preset m.fork)
      simp only at nextEpoch
      rw [nextEpoch, getCurrentEpoch_toNat m.state]
      exact nextSlot_epoch_of_boundary sum boundary
    have nextBound : (getCurrentEpoch deposited).toNat + 1 ≤ high + 1 := by
      rw [epochD]; omega
    have nextNat :
        (getCurrentEpoch deposited + 1).toNat = (getCurrentEpoch deposited).toNat + 1 := by
      have fits := (getCurrentEpoch last.state).toNat_lt
      rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt]
      rw [epochD]; omega
    have facts : PassFacts (config := config) x high deposited :=
      { electraX := electra, electraP := mFork, caps := caps, delay := delay, within := within,
        life := lifeXM.trans (lifeMC.trans lifeCD), cap := capXM.trans (capMC.trans capCD),
        orderedX := orderedX, invariantP := (orderedCD orderedC).1, cappedX := cappedX,
        next := nextBound, nextNat := nextNat }
    have shapeD : Shape (queueX x electra) (getCurrentEpoch x.state) n deposited :=
      shapeCached.carry queueCD lifeCD
    obtain ⟨r, shapeMiddle, lifePM, credits⟩ := pass_step_targets facts shapeD consolidatedOk
    refine ⟨r, ?_, fun {events} replayed T => ?_⟩
    · have trace := processEpoch_trace epochOk
      change EpochTrace _ (EpochStage.prefixStages ++ [.payments, .effectiveBalances,
        .slashingsReset, .randaoReset, .history, .participation, .syncCommittees,
        .proposerLookahead, .ptcWindow]) _ _ at trace
      obtain ⟨middle', head, tailTrace⟩ := EpochTrace.append_iff.mp trace
      have midEq : middle' = middle := by
        have h1 : epochBeforePayments config checks cached = .ok middle' :=
          (epochBeforePayments_eq_run config checks cached).trans
            (EpochTrace.run_ok_iff.mpr head)
        rw [h1] at cutOk
        exact Except.ok.inj cutOk
      subst midEq
      obtain ⟨lifeTail, -, queueTail, -⟩ := prefix_rel mFork (by
        intro k member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact fun h => by cases h) tailTrace
      have shapeEpoched := shapeMiddle.carry queueTail lifeTail
      have shapeAdvanced : Shape (queueX x electra) (getCurrentEpoch x.state) (n + r)
          advanced := by
        rw [← afterEq]
        exact shapeEpoched.carry rfl (.of_data rfl)
      exact upgrades_shape (advanced := ⟨m.fork, advanced⟩) mFork early shapeAdvanced upgrades
    · have eventsEq : events = recorded ++ crossings :=
        Except.ok.inj (replayed.symm.trans (Step.balanceEvents_epoch_slot ok cachedOk nextOk
          boundary recordOk slotOk crossingOk))
      have rewardsNo := rewards_noConsolidations (pre := (scored, [])) (by simp) rewardReplay
      have f1 : rewardEvents.filter (fun e => decide (e.source = .consolidations)) = [] :=
        List.filter_eq_nil_iff.mpr fun e member => by simpa using rewardsNo e member
      have f2 : crossings.filter (fun e => decide (e.source = .consolidations)) = [] :=
        List.filter_eq_nil_iff.mpr fun e member => by
          simp [upgradeBalanceReplay_crossing crossingOk e member]
      rw [eventsEq, recordedEq]
      simp only [List.append_assoc, List.filter_append, f1, f2]
      simpa [List.filter_cons, creditedAt, PinDrift.Internal.keyCredit, actualBalanceAt] using
        credits T
  · simp only [epochIfLast, boundary, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at epochOk
    subst epochOk
    refine ⟨0, ?_, fun {events} replayed T => ?_⟩
    · have shapeAdvanced : Shape (queueX x electra) (getCurrentEpoch x.state) (n + 0)
          advanced := by
        rw [← afterEq]
        exact shapeCached.carry rfl (.of_data rfl)
      exact upgrades_shape (advanced := ⟨m.fork, advanced⟩) mFork early shapeAdvanced upgrades
    · have eventsEq : events = crossings := by
        simpa [Step.balanceEvents, cachedOk, nextOk, boundary, slotOk, crossingOk, pure,
          Except.pure,
          bind, Except.bind] using replayed.symm
      subst eventsEq
      have none : (events.filter (·.source = .consolidations)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro e member
        simp [upgradeBalanceReplay_crossing crossingOk e member]
      simp [none]

/-- A block keeps the shape of the queue: it only appends entries that are new since X. -/
private theorem block_step {f : Fork} {e0 : Epoch} {L : List PendingConsolidation} {n : ℕ}
    (electra : .pectra ≤ f) (early : f < .glamsterdam)
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {engine : ExecutionEngine preset f} {signed : SignedBeaconBlock preset f}
    {s t : BeaconState preset f}
    (ok : applySignedBlock config checks engine s signed true = .ok t)
    (started : e0 ≤ getCurrentEpoch s) (shape : Shape L e0 n s) : Shape L e0 n t := by
  have grown := ConsolidationQueueRise.appendStep_processBlock (Nat.le_trans (by decide) electra)
    early delay (applySignedBlock_ok ok).2.1
  exact shape.grow electra grown.2.2 grown.2.1 started

/-- The consolidation credits of a run from X to the targets in `T` are within the caps.

The caps are those of the entries it reads whose target is in `T`. -/
private theorem run_credits_targets {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (electra : .pectra ≤ x.fork) (high : ℕ)
    (within : high + 2 ≤ (getCurrentEpoch x.state).toNat +
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    ∃ n, Shape (queueX x electra) (getCurrentEpoch x.state) n y.state ∧
      ∀ T : Finset ℕ,
        (T.sum fun i => ((events.filter (·.source = .consolidations)).map
          (PinDrift.Internal.keyCredit i)).sum) ≤
          ((((queueX x electra).take n).filter fun c => c.targetIndex.toNat ∈ T).map
            (capBound x high)).sum := by
  induction tail generalizing events with
  | nil =>
    cases replayed
    refine ⟨0, ⟨[], ?_, fun c member => by simp at member⟩, fun T => by simp⟩
    rw [fundingSources_eq electra]
    simp [queueX]
  | @snoc middle last pre step ih =>
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    have epochStep := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
    obtain ⟨n, shape, bound⟩ := ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early)
      (by omega) priorOk
    have inFork : .pectra ≤ middle.fork :=
      Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
    have started : getCurrentEpoch x.state ≤ getCurrentEpoch middle.state :=
      currentEpoch_le_of_chainSteps pre.chainSteps
    have beforeFork : middle.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have growth : ∀ {r : ℕ} {T : Finset ℕ},
        ((((queueX x electra).take n).filter fun c => c.targetIndex.toNat ∈ T).map
          (capBound x high)).sum +
        (((((queueX x electra).drop n).take r).filter fun c => c.targetIndex.toNat ∈ T).map
          (capBound x high)).sum =
        ((((queueX x electra).take (n + r)).filter fun c => c.targetIndex.toNat ∈ T).map
          (capBound x high)).sum := by
      intro r T
      rw [List.take_add, List.filter_append, List.map_append, List.sum_append]
    have stepResult : ∃ r, Shape (queueX x electra) (getCurrentEpoch x.state) (n + r) last.state ∧
        ∀ {added : List (BalanceEvent preset)}, step.balanceEvents = .ok added → ∀ T : Finset ℕ,
          (T.sum fun i => ((added.filter (·.source = .consolidations)).map
            (PinDrift.Internal.keyCredit i)).sum) ≤
            (((((queueX x electra).drop n).take r).filter fun c => c.targetIndex.toNat ∈ T).map
              (capBound x high)).sum := by
      cases step with
      | block engine signed due ok =>
        refine ⟨0, block_step inFork early (by omega) ok started shape, fun {added} addedOk T => ?_⟩
        have none : (added.filter (·.source = .consolidations)) = [] :=
          List.filter_eq_nil_iff.mpr fun e member => by
            simpa using blockReplay_noConsolidations inFork early engine _ _
              (Step.balanceEvents_block early addedOk) e member
        simp [none]
      | slot ok =>
        obtain ⟨r, shapeLast, credits⟩ := slot_step_targets shared pre genesis caps delay electra
          high within ok early endEpoch shape
        exact ⟨r, shapeLast, fun {added} addedOk => credits addedOk⟩
    obtain ⟨r, shapeLast, credits⟩ := stepResult
    refine ⟨n + r, shapeLast, fun T => ?_⟩
    have bound := bound T
    by_cases selected : (getCurrentEpoch middle.state).toNat ≤ high + 1
    · simp only [selected, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
      obtain ⟨added, addedOk, rfl⟩ := rest
      have := credits addedOk T
      have growth' := growth (r := r) (T := T)
      simp only [List.filter_append, List.map_append, List.sum_append, Finset.sum_add_distrib]
      omega
    · simp only [selected, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      have growth' := growth (r := r) (T := T)
      omega

/-- The caps of the entries of a queue, as the caps of their sources that X lets move. -/
private theorem capBound_sum (x : ForkedBeaconState preset) (high : ℕ)
    (queue : List PendingConsolidation) :
    (queue.map (capBound x high)).sum =
      ((((queue.filterMap fun c => x.state.validators.data[c.sourceIndex.toNat]?).filter
        fun v => !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)).map
          fun v => (withdrawalMaxEffectiveBalance preset x.fork v).toNat).sum) := by
  induction queue with
  | nil => simp
  | cons c rest ih =>
    cases lookup : x.state.validators.data[c.sourceIndex.toNat]? with
    | none => simpa [capBound, lookup] using ih
    | some v =>
      by_cases due : v.slashed = false ∧ v.withdrawableEpoch.toNat ≤ high + 1
      · simp [capBound, lookup, due, ih]
      · have : ¬ (!v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)) = true := by
          simpa [Bool.not_eq_true'] using due
        simp [capBound, lookup, due, this, ih]

/-! ## Credits to exiting keys, by pass -/

/-- No deposit credits a key that is exited and not withdrawable at each deposit event of a run.

`exitedAt` is that fact at the state before each deposit event of a slot step.

A block deposit needs none: from Electra it raises no balance. -/
theorem
  _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Run.exiting_deposit_credit_zero_of_exited
  {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (high : ℕ) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events) (i : ℕ)
    (exitedAt : ∀ {u w : ForkedBeaconState preset} (ok : advanceSlotAcross config checks u = .ok w),
      tail.Contains (Step.slot ok) → ∀ {es : List (BalanceEvent preset)},
        (Step.slot ok : Step config checks u w).balanceEvents = .ok es →
        ∀ e ∈ es, e.source = .deposits → ∃ v : Validator,
          e.before.state.validators.data[i]? = some v ∧ v.exitEpoch.toNat < 2 ^ 64 - 1 ∧
          (getCurrentEpoch e.before.state).toNat < v.withdrawableEpoch.toNat) :
    ((events.filter (·.source = .deposits)).map (PinDrift.Internal.keyCredit i)).sum = 0 := by
  have located := (PinDrift.Internal.run_located tail electra early high replayed).1
  apply List.sum_eq_zero
  intro n member
  obtain ⟨e, filtered, rfl⟩ := List.mem_map.mp member
  obtain ⟨inEvents, sourceEq⟩ := List.mem_filter.mp filtered
  simp only [decide_eq_true_eq] at sourceEq
  rcases located e inEvents sourceEq with unconditional | ⟨u, w, ok, es, contains, replayedEs,
      inStep, keeps⟩
  · have := unconditional i
    simp only [PinDrift.Internal.keyCredit]
    omega
  · obtain ⟨v, read, exited, held⟩ := exitedAt ok contains replayedEs e inStep sourceEq
    have same := keeps i v read exited held
    simp [PinDrift.Internal.keyCredit, actualBalanceAt, same]

/-- The deposit bound along a run.

Along C's run, no deposit credits a key that exits at the run's start.

The key stays not withdrawable through the run's end.

`kept` is the withdrawable-kept fact at the state before each deposit event of a slot step.

A block deposit needs none: from Electra it raises no balance.

It says that an assigned exit stays (`RegistryLifecycle`).

It says that once the exit is set, the withdrawable epoch only rises (`WithdrawableKept`).

It also says that the epoch of each event's state is at most the run's last epoch. -/
private theorem Run.exiting_deposit_credit_zero_of_kept {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (high : ℕ) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (kept : ∀ {u w : ForkedBeaconState preset} (ok : advanceSlotAcross config checks u = .ok w),
      tail.Contains (Step.slot ok) → ∀ {es : List (BalanceEvent preset)},
        (Step.slot ok : Step config checks u w).balanceEvents = .ok es →
        ∀ e ∈ es, e.source = .deposits →
          RegistryLifecycle x.state e.before.state ∧ WithdrawableKept x.state e.before.state ∧
          getCurrentEpoch e.before.state ≤ getCurrentEpoch y.state)
    (i : ℕ) (v : Validator) (found : x.state.validators.data[i]? = some v)
    (exited : v.exitEpoch.toNat < 2 ^ 64 - 1)
    (held : (getCurrentEpoch y.state).toNat < v.withdrawableEpoch.toNat) :
    ((events.filter (·.source = .deposits)).map (PinDrift.Internal.keyCredit i)).sum = 0 :=
  PinDrift.Internal.Run.exiting_deposit_credit_zero_of_exited tail electra early high replayed i
    (by
      intro u w ok contains es replayedEs e inStep sourceEq
      obtain ⟨life, withdrawal, epoch⟩ := kept ok contains replayedEs e inStep sourceEq
      obtain ⟨w, read, lifecycle⟩ := life.validators i v found
      have assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
        rw [far] at exited
        exact absurd exited (Nat.lt_irrefl _)
      have sameExit := lifecycle.exitEpoch assigned
      have later := UInt64.le_iff_toNat_le.mp (withdrawal i v w found read assigned).1
      have now := UInt64.le_iff_toNat_le.mp epoch
      exact ⟨w, read, by rw [sameExit]; exact exited, by omega⟩)

/-- Along C's run from Fulu, no deposit credits a key that exits at the run's start.

The key stays not withdrawable through the run's end.

The withdrawable-kept fact at each deposit event of a slot step is `Run.events_kept`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Run.exiting_deposit_credit_zero {g
  x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (fulu : .fusaka ≤ x.fork) (early : y.fork < .glamsterdam)
    (high : ℕ) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (i : ℕ) (v : Validator) (found : x.state.validators.data[i]? = some v)
    (exited : v.exitEpoch.toNat < 2 ^ 64 - 1)
    (held : (getCurrentEpoch y.state).toNat < v.withdrawableEpoch.toNat) :
    ((events.filter (·.source = .deposits)).map (PinDrift.Internal.keyCredit i)).sum = 0 :=
  Run.exiting_deposit_credit_zero_of_kept tail (Nat.le_trans (by decide) fulu) early high replayed
    (fun {_ _} ok contained {_} replayedEs e member source =>
      let kept := PinDrift.Internal.Run.events_kept shared genesis tail fulu early ok contained
        replayedEs
        e member source
      ⟨kept.1, kept.2.1, kept.2.2.1⟩)
    i v found exited held

/-- A step that starts a key's exit credits no deposit to it.

A slot step's pending deposits come after its registry updates, which postpone the key.

The exit and withdrawable epochs at the step's end are those at the input of its deposits. -/
private theorem Step.charge_deposit_credit_zero {a b : ForkedBeaconState preset}
    (step : Step config checks a b) (fulu : .fusaka ≤ a.fork) (early : b.fork < .glamsterdam)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events)
    (i : ℕ) (inside : i < a.state.validators.data.size) (w : Validator)
    (found : b.state.validators.data[i]? = some w) (exited : w.exitEpoch.toNat < 2 ^ 64 - 1)
    (held : (getCurrentEpoch b.state).toNat < w.withdrawableEpoch.toNat) :
    ((events.filter (·.source = .deposits)).map (PinDrift.Internal.keyCredit i)).sum = 0 := by
  refine PinDrift.Internal.Run.exiting_deposit_credit_zero_of_exited (Run.nil.snoc step)
    (Nat.le_trans (by decide) fulu) early (getCurrentEpoch b.state).toNat
    (DirectSafety.Apriori.Internal.single_balanceEvents step replayed) i ?_
  intro u w' ok contains es replayedEs e member source
  cases contains with
  | last =>
    obtain ⟨kept, -, same, stay, -⟩ :=
      PinDrift.Internal.Step.deposit_input ok fulu early replayedEs e member source
    obtain ⟨v, readV⟩ : ∃ v, e.before.state.validators.data[i]? = some v :=
      ⟨_, Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le inside kept.life.size_le)⟩
    obtain ⟨w'', read, exit, wd⟩ := stay i v readV
    rw [found, Option.some.injEq] at read
    subst read
    have epochLe := UInt64.le_iff_toNat_le.mp
      (Step.slot ok : Step config checks a b).chainStep.currentEpoch_le
    refine ⟨v, readV, by rw [← exit]; exact exited, ?_⟩
    rw [same, ← wd]
    omega
  | earlier member _ => cases member

/-- Along a run from the step that starts a key's exit, no deposit credits the key.

The key is exited and not withdrawable at the run's end.

The step is counted by the replay. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Run.charge_deposit_credit_zero {g a
  b y : ForkedBeaconState preset}
    (shared : Run config checks g a) (genesis : Genesis (config := config) (checks := checks) g)
    (step : Step config checks a b) (post : Run config checks b y) (fulu : .fusaka ≤ a.fork)
    (early : y.fork < .glamsterdam) (high : ℕ)
    (counted : (getCurrentEpoch a.state).toNat ≤ high + 1) {events : List (BalanceEvent preset)}
    (replayed : ((Run.nil.snoc step).append post).balanceEvents high = .ok events)
    (i : ℕ) (inside : i < a.state.validators.data.size) (w : Validator)
    (found : b.state.validators.data[i]? = some w) (exited : w.exitEpoch.toNat < 2 ^ 64 - 1)
    (held : (getCurrentEpoch y.state).toNat < w.withdrawableEpoch.toNat) :
    ((events.filter (·.source = .deposits)).map (PinDrift.Internal.keyCredit i)).sum = 0 := by
  have bEarly : b.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early
  obtain ⟨es, replayedS⟩ := step.balanceEvents_ok bEarly
  obtain ⟨later, replayedP⟩ := post.balanceEvents_ok early high
  have one : (Run.nil.snoc step : Run config checks a b).balanceEvents high = .ok es := by
    simp [Run.balanceEvents, counted, replayedS, pure, Except.pure]
    rfl
  rw [DirectSafety.Apriori.Internal.balanceEvents_append _ _ high one replayedP] at replayed
  obtain rfl := Except.ok.inj replayed
  have heldB : (getCurrentEpoch b.state).toNat < w.withdrawableEpoch.toNat :=
    Nat.lt_of_le_of_lt (UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps))
      held
  have first := Step.charge_deposit_credit_zero step fulu bEarly replayedS i inside w found exited
    heldB
  have second := PinDrift.Internal.Run.exiting_deposit_credit_zero (shared.append (Run.nil.snoc
    step)) genesis post
    (Nat.le_trans fulu step.chainStep.fork_le) early high replayedP i w found exited held
  simp only [List.filter_append, List.map_append, List.sum_append]
  omega

/-- The consolidation credits to the keys in `T` along the run.

They are at most the caps at X of the due entries of X's queue whose target is in `T`.

Each entry credits only its target, so the sum over the entries splits by target. -/
theorem
  _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Run.consolidation_credits_le_X_targets {g
  x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset)
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (high : ℕ) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (withinDelay : high + 2 ≤
      (getCurrentEpoch x.state).toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) (T : Finset ℕ) :
    (T.sum fun i => ((events.filter (·.source = .consolidations)).map (PinDrift.Internal.keyCredit
      i)).sum) ≤
      ((((((x.state.pendingConsolidations electra).data.toList.filter fun c =>
          c.targetIndex.toNat ∈ T).filterMap fun c =>
        x.state.validators.data[c.sourceIndex.toNat]?).filter fun v =>
          !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)).map fun v =>
            (withdrawalMaxEffectiveBalance preset x.fork v).toNat).sum) := by
  obtain ⟨n, -, bound⟩ := run_credits_targets shared genesis caps delay electra high withinDelay
    tail early endEpoch replayed
  rw [← capBound_sum]
  refine Nat.le_trans (bound T) ?_
  have split := List.take_append_drop n (x.state.pendingConsolidations electra).data.toList
  conv_rhs => rw [← split, List.filter_append, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

end PinKeys

end

section

/-! ## A validator created in a step has no exit assigned -/

namespace PinKeys

open Base Uint64 Models DirectSafety

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-- Every validator from position `n` on has no exit epoch assigned. -/
private def ExitFarFrom (n : ℕ) {f : Fork} (s : BeaconState preset f) : Prop :=
  ∀ i v, n ≤ i → s.validators.data[i]? = some v → v.exitEpoch = FAR_FUTURE_EPOCH

/-- A state with the same registry has no exit assigned from position `n` either. -/
private theorem ExitFarFrom.of_data {n : ℕ} {f g : Fork} {s : BeaconState preset f}
    {t : BeaconState preset g} (same : t.validators.data = s.validators.data)
    (holds : ExitFarFrom n s) : ExitFarFrom n t := by
  intro i v large found
  rw [same] at found
  exact holds i v large found

/-- A registry that does not reach position `n` has no validator from there on. -/
private theorem ExitFarFrom.of_size {n : ℕ} {f : Fork} {s : BeaconState preset f}
    (small : s.validators.data.size ≤ n) : ExitFarFrom n s := by
  intro i v large found
  have := (Array.getElem?_eq_some_iff.mp found).1
  omega

/-- A write that keeps the exit epoch of its validator keeps the later validators unassigned. -/
private theorem ExitFarFrom.of_set {n position : ℕ} {f : Fork} {s t : BeaconState preset f}
    {old v : Validator} (found : getValidatorAt s position = .ok old)
    (set : s.setValidatorAt position v = .ok t) (same : v.exitEpoch = old.exitEpoch)
    (holds : ExitFarFrom n s) : ExitFarFrom n t := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  intro i w large got
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.getElem?_set] at got
  split at got
  · rename_i place
    subst place
    cases got
    rw [same]
    exact holds position old large (getValidatorAt_eq_ok_iff.mp found)
  · exact holds i w large got

/-- A pending deposit appends a validator with no exit epoch. -/
private theorem ExitFarFrom.of_apply {n : ℕ} {f : Fork} {s t : BeaconState preset f}
    {deposit : PendingDeposit}
    (ok : Consensus.applyPendingDeposit config checks s deposit = .ok t) (holds : ExitFarFrom n s) :
    ExitFarFrom n t := by
  rcases applyPendingDeposit_cases ok with rfl | ⟨index, raised⟩ | ⟨_, added⟩
  · exact holds
  · exact holds.of_data (congrArg (·.data) (increaseBalance_validators raised))
  · intro i v large found
    rw [addValidatorToRegistry_validators_eq_push added, Array.getElem?_push] at found
    split at found
    · cases found
      rfl
    · exact holds i v large found

/-- Applying the pending deposits assigns no exit from position `n` on. -/
private theorem ExitFarFrom.of_deposits {n : ℕ} {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} (ok : Consensus.processPendingDeposits config checks s electra = .ok t)
    (holds : ExitFarFrom n s) : ExitFarFrom n t := by
  obtain ⟨_, _, _, _, next, _, _, _, _, _, _, _, _, folded, rfl⟩ :=
    processPendingDeposits_applied ok
  have kept : ExitFarFrom n next :=
    foldlM_ok_invariant (g := Consensus.applyPendingDeposit config checks)
      (fun u : BeaconState preset f => ExitFarFrom n u)
      (fun _ _ _ before step => ExitFarFrom.of_apply step before) holds folded
  exact kept

/-- The effective-balance updates write only effective balances. -/
private theorem ExitFarFrom.of_updates {n : ℕ} {f : Fork}
    {s t : BeaconState preset f} (ok : Consensus.processEffectiveBalanceUpdates s = .ok t)
    (holds : ExitFarFrom n s) : ExitFarFrom n t := by
  unfold Consensus.processEffectiveBalanceUpdates at ok
  refine foldlM_ok_invariant (fun u : BeaconState preset f => ExitFarFrom n u)
    (fun _ _ _ before step => ?_) holds ok
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at step
  obtain ⟨validator, found, _, _, _, _, set⟩ := step
  exact before.of_set found set rfl

/-- An epoch appends validators only in its pending deposits, after the registry updates.

So a validator that the epoch creates has no exit epoch. -/
private theorem ExitFarFrom.of_epoch {n : ℕ} {f : Fork} {s t : BeaconState preset f}
    (electra : .pectra ≤ f) (ok : Consensus.processEpoch config checks s = .ok t)
    (small : s.validators.data.size ≤ n) : ExitFarFrom n t := by
  obtain ⟨justified, scored, rewarded, registered, slashed, reset, deposited, consolidated,
    settled, updated, justifiedOk, scoredOk, rewardedOk, registeredOk, slashedOk, resetOk,
    depositedOk, consolidatedOk, settledOk, updatedOk, rest⟩ :=
    EpochTrace.through_effectiveBalances (processEpoch_trace ok)
  have keeps {k : EpochStage} {a b : BeaconState preset f}
      (other : k ≠ .rewards ∧ k ≠ .registry ∧ k ≠ .slashings ∧ k ≠ .pendingDeposits ∧
        k ≠ .pendingConsolidations ∧ k ≠ .effectiveBalances)
      (computed : EpochStage.action config checks k a = .ok b) : b.validators = a.validators :=
    (EpochStage.action_cases.mp computed).records other |>.1
  -- The first six stages keep the size of the registry.
  have size : reset.validators.data.size = s.validators.data.size := by
    have one : justified.validators.data.size = s.validators.data.size :=
      congrArg (·.data.size) (keeps (k := .justification) ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
        justifiedOk)
    have two : scored.validators.data.size = justified.validators.data.size :=
      congrArg (·.data.size) (keeps (k := .inactivity) ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
        scoredOk)
    have three := (processRewardsAndPenalties_sameSizes
      (EpochStage.action_cases.mp rewardedOk)).1
    have four := (sameSizes_processRegistryUpdates (EpochStage.action_cases.mp registeredOk)).1
    have five := (sameSizes_processSlashings (EpochStage.action_cases.mp slashedOk)).1
    have six : reset.validators.data.size = slashed.validators.data.size :=
      congrArg (·.data.size) (keeps (k := .eth1Reset) ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
        resetOk)
    omega
  have atReset : ExitFarFrom n reset := .of_size (by omega)
  -- Pending deposits append validators with no exit.
  have atDeposited : ExitFarFrom n deposited := by
    have edge := EpochStage.action_cases.mp depositedOk
    simp only [EpochStage.Edge, electra, ↓reduceDIte] at edge
    exact atReset.of_deposits edge
  have atConsolidated : ExitFarFrom n consolidated :=
    atDeposited.of_data (congrArg (·.data)
      ((EpochStage.action_cases.mp consolidatedOk).validators_eq ⟨nofun, nofun, nofun⟩))
  have atSettled : ExitFarFrom n settled :=
    atConsolidated.of_data (congrArg (·.data) ((EpochStage.action_cases.mp settledOk).validators_eq
      ⟨nofun, nofun, nofun⟩))
  have atUpdated : ExitFarFrom n updated :=
    atSettled.of_updates (EpochStage.action_cases.mp updatedOk)
  -- The seven later stages keep the validators.
  have same : t.validators = updated.validators :=
    EpochTrace.transport (fun a b : BeaconState preset f => b.validators = a.validators)
      (fun _ => rfl) (fun one two => two.trans one)
      (fun k member a b computed => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        exact keeps (by rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩) computed) rest
  exact atUpdated.of_data (congrArg (·.data) same)

/-- From Electra, a step before Gloas leaves every validator that it creates with no exit epoch. -/
private theorem ExitFarFrom.of_chainStep {a b : ForkedBeaconState preset}
    (step : ChainStep config checks a b) (electra : .pectra ≤ a.fork)
    (early : a.fork < .glamsterdam) : ExitFarFrom a.state.validators.data.size b.state := by
  cases step with
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    obtain ⟨next, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok slotOk
    obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
    have atEpoched : ExitFarFrom a.state.validators.data.size epoched := by
      unfold epochIfLast at epochedOk
      split at epochedOk
      · exact ExitFarFrom.of_epoch electra epochedOk (by rw [cachedEq])
      · cases epochedOk
        exact .of_size (by rw [cachedEq])
    have atAdvanced : ExitFarFrom a.state.validators.data.size { epoched with slot := next } :=
      atEpoched.of_data rfl
    exact (processUpgrades_induction (config := config) (checks := checks)
      (forked := ⟨a.fork, { epoched with slot := next }⟩) (after := b)
      (property := fun post => ExitFarFrom a.state.validators.data.size post.state ∧
        .pectra ≤ post.fork)
      (fun {pre post} kept ok =>
        ⟨kept.1.of_data (upgradeNext_validators_of_electra kept.2 ok),
          Nat.le_trans kept.2 (Nat.le_of_lt post.property)⟩)
      ⟨atAdvanced, electra⟩ upgrades).1
  | block engine signed validate ok =>
    obtain ⟨input, last, started, operated, -, synced⟩ :=
      processBlock_operationsInput (applySignedBlock_ok ok).2.1
    have same := OperationsInput.validators_eq early started
    have fresh := processOperations_new_validator_epochs_unassigned operated
    intro i v large found
    have lastFound : last.validators.data[i]? = some v := by
      split at synced
      · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
        exact found
      · cases synced
        exact found
    exact (fresh i v (by rw [same]; exact large) lastFound).2

/-- Along a run from Electra, a validator can gain an exit epoch only through a departure charge.

The charge is at that exit epoch. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Run.charge_of_exit {x y :
  ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (i : ℕ) (unset : ∀ v, x.state.validators.data[i]? = some v → v.exitEpoch = FAR_FUTURE_EPOCH)
    (v : Validator) (found : y.state.validators.data[i]? = some v)
    (assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    ∃ c ∈ tail.departureCharges, c.index = i ∧ c.epoch = v.exitEpoch.toNat := by
  cases initial : x.state.validators.data[i]? with
  | some w => exact tail.departure_charge_of_assigned i w v initial found (unset w initial) assigned
  | none =>
    obtain ⟨m, n, pre, step, post, rfl, absent, arrived⟩ := Run.split_at_flip tail
      (fun z => i < z.state.validators.data.size)
      (Nat.not_lt.mpr (Array.getElem?_eq_none_iff.mp initial))
      (Array.getElem?_eq_some_iff.mp found).1
    have electraM : .pectra ≤ m.fork := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
    have earlyM : m.fork < .glamsterdam := Nat.lt_of_le_of_lt step.chainStep.fork_le
      (Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early)
    have read := Array.getElem?_eq_getElem arrived
    have pending := ExitFarFrom.of_chainStep step.chainStep electraM earlyM i _
      (Nat.le_of_not_lt absent) read
    obtain ⟨c, member, index, epoch⟩ :=
      post.departure_charge_of_assigned i _ v read found pending assigned
    exact ⟨c, by rw [Run.departureCharges_append]; exact List.mem_append_right _ member, index,
      epoch⟩

end PinKeys

end

section

/-! ## PinSeatDebits -/

namespace PinSeatDebits

open Base Uint64 Models DirectSafety

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The participant reward at a state is at most the envelope of a total.

The total of the state is within three halves of that total. -/
private theorem syncReward_le_envelope {fork : Fork} {s : BeaconState preset fork}
    {reward T : Gwei} (rewardOk : syncParticipantReward s = .ok reward)
    (totalOk : getTotalActiveBalance s = .ok T) (total : ℕ) (band : 2 * T.toNat ≤ 3 * total) :
    reward.toNat ≤ PinTerms.syncEnvelope preset total := by
  simp only [syncParticipantReward, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff] at rewardOk
  obtain ⟨read, readOk, perIncrement, perOk, rewardOk⟩ := rewardOk
  obtain rfl : T = read := Except.ok.inj (totalOk.symm.trans readOk)
  obtain ⟨increments, incrementsOk, base, baseOk, weighted, weightedOk, perWeight, perWeightOk,
    perSlot, perSlotOk, rewardOk⟩ := rewardOk
  rw [divChecked_ok_iff] at incrementsOk perWeightOk perSlotOk rewardOk
  rw [mulChecked_ok_iff] at baseOk weightedOk
  have weightValue : SYNC_REWARD_WEIGHT.toNat = 2 := rfl
  have denominator : WEIGHT_DENOMINATOR.toNat = 64 := rfl
  rw [weightValue] at weightedOk
  rw [denominator] at perWeightOk
  have rootLe : Nat.sqrt T.toNat ≤ Nat.sqrt (3 * total / 2) :=
    Nat.sqrt_le_sqrt (by omega)
  have baseLe : base.toNat ≤ preset.BASE_REWARD_FACTOR.toNat * (Nat.sqrt (3 * total / 2) + 2) := by
    rw [baseOk.2, incrementsOk.2, toNat_getBaseRewardPerIncrement perOk, Nat.mul_comm]
    rcases Nat.eq_zero_or_pos T.toNat with zero | positive
    · simp [zero]
    · exact (div_mul_div_sqrt_le positive _).trans (Nat.mul_le_mul_left _ (by omega))
  unfold PinTerms.syncEnvelope
  rw [weightValue, denominator, rewardOk.2, perSlotOk.2, perWeightOk.2, weightedOk.2]
  exact Nat.div_le_div_right (Nat.div_le_div_right (Nat.div_le_div_right
    (Nat.mul_le_mul_right 2 baseLe)))

/-- The proposer's share of a reward is at most that share of any bound on the reward. -/
private theorem syncProposer_le {reward proposer : Gwei} {bound : ℕ} (le : reward.toNat ≤ bound)
    (ok : liftAccessor (liftArith (do
        Uint64.divChecked (← Uint64.mulChecked reward PROPOSER_WEIGHT)
          (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT))) = Except.ok proposer) :
    proposer.toNat ≤ bound * PROPOSER_WEIGHT.toNat /
      (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) := by
  simp only [liftAccessor_ok, liftArith, mapError_ok_iff, bind_ok_iff] at ok
  obtain ⟨product, productOk, quotientOk⟩ := ok
  rw [divChecked_ok_iff] at quotientOk
  rw [mulChecked_ok_iff] at productOk
  have difference : (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT).toNat = 56 := rfl
  have proposerWeight : PROPOSER_WEIGHT.toNat = 8 := rfl
  have denominator : WEIGHT_DENOMINATOR.toNat = 64 := rfl
  rw [quotientOk.2, productOk.2, difference, proposerWeight, denominator]
  exact Nat.div_le_div_right (Nat.mul_le_mul_right _ le)

/-- The sync reward of a seat at the envelope of a total, with its proposer share. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.syncSeatEnvelope (preset : Preset)
  (total : ℕ) : ℕ :=
  PinTerms.syncEnvelope preset total + PinTerms.syncEnvelope preset total * PROPOSER_WEIGHT.toNat /
    (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat)

/-- The credits of an event over a set of keys are at most its credits over the registry. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.keys_credits_le (S : Finset ℕ) (e :
  BalanceEvent preset) :
    ∑ j ∈ S, (actualBalanceAt e.after j - actualBalanceAt e.before j) ≤ e.credits := by
  unfold BalanceEvent.credits
  refine Finset.sum_le_sum_of_ne_zero fun j _ positive => Finset.mem_range.mpr ?_
  by_contra outside
  apply positive
  simp [actualBalanceAt, Array.getElem?_eq_none (Nat.le_of_not_lt outside)]

/-- The events of a replay record no sync pass. -/
private def NoSync {fork : Fork} (pre : BalanceReplay preset fork) : Prop :=
  ∀ e ∈ pre.2, e.source ≠ .sync

/-- A pass that records no event keeps the replay free of sync events. -/
private theorem NoSync.carry {fork : Fork}
    {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
    {p q : BalanceReplay preset fork} (held : NoSync p) (ok : carryBalance action p = .ok q) :
    NoSync q := by
  intro e member
  rw [(PinDrift.Internal.carryBalance_cases ok).2] at member
  exact held e member

/-- A recorded pass that is not the sync pass keeps the replay free of sync events. -/
private theorem NoSync.record {fork : Fork} {source : BalanceSource}
    {limits : BeaconState preset fork → Except TransitionError (Nat × Nat)}
    {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
    {p q : BalanceReplay preset fork} (held : NoSync p)
    (ok : recordBalance source limits action p = .ok q) (notSync : source ≠ .sync) :
    NoSync q := by
  intro e member
  obtain ⟨_, _, _, _, events⟩ := recordBalance_single ok
  rcases PinEventsKept.mem_or_source_of_append events rfl member with old | new
  · exact held e old
  · rw [new]
    exact notSync

/-- The effective balance of a key at a state of a run from genesis is at most the largest cap. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.effectiveAt_le_capMax {g m :
  ForkedBeaconState preset}
    (run : Run config checks g m) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (early : m.fork < .glamsterdam) (v : ℕ) :
    effectiveAt m v ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := by
  cases found : m.state.validators.data[v]? with
  | none => simp [effectiveAt, found]
  | some w =>
    exact (DirectSafety.Apriori.Internal.effectiveAt_le_withdrawalMax run genesis caps early
      found).trans ((withdrawalMaxEffectiveBalance_le_largestEffectiveBalance preset m.fork w).trans
        (max_le (UInt64.le_iff_toNat_le.mp (UInt64.le_trans caps.activation caps.compounding))
          (max_le (UInt64.le_iff_toNat_le.mp caps.compounding) le_rfl)))

/-- The replay of a block from Altair ends with its one sync pass, after events of other sources.

The pass is the sync aggregate of the block, applied at the state that its other passes leave. -/
private theorem blockReplay_sync_split {fork : Fork} {a t : BeaconState preset fork}
    (early : fork < .glamsterdam) (altair : .altair ≤ fork) {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork} {events : List (BalanceEvent preset)}
    (replay : blockBalanceReplay (config := config) (checks := checks) early engine a block =
      .ok (t, events)) :
    ∃ (c : BeaconState preset fork) (rest : List (BalanceEvent preset))
      (aggregate : SyncAggregate preset) (credit debit : ℕ),
      events = rest ++ [⟨.sync, ⟨fork, c⟩, ⟨fork, t⟩, credit, debit⟩] ∧
      (∀ i, (rest.map (PinDrift.Internal.syncDebit i)).sum = 0) ∧
      (∀ i, (rest.map (PinDrift.Internal.syncCredit i)).sum = 0) ∧
      processSyncAggregate config checks c altair aggregate = .ok t := by
  have normalized := replay
  unfold blockBalanceReplay at normalized
  simp only [altair, ↓reduceDIte] at normalized
  simp only [← bind_assoc, DirectSafety.Apriori.Internal.except_dite_bind] at normalized
  simp only [bind_assoc] at normalized
  simp only [bind_ok_iff, ensure_ok_iff] at normalized
  obtain ⟨headed, headedOk, executed, executedOk, revealed, revealedOk, voted, votedOk, _, _, _,
    _, proposed, proposedOk, slashed, slashedOk, attested, attestedOk, deposited, depositedOk,
    exited, exitedOk, changed, changedOk, consolidated, requestsOk, syncOk⟩ := normalized
  have start : NoSync ((a, []) : BalanceReplay preset fork) := fun _ member => by cases member
  have one := start.carry headedOk
  have two : NoSync executed := by
    split at executedOk
    · exact one.record executedOk (by decide)
    · cases executedOk
      exact one
  have three := two.carry revealedOk
  have four := three.carry votedOk
  have five := foldlM_ok_invariant NoSync
    (fun _ _ _ prior computed => prior.record computed (by decide)) four proposedOk
  have six := foldlM_ok_invariant NoSync
    (fun _ _ _ prior computed => prior.record computed (by decide)) five slashedOk
  have seven := foldlM_ok_invariant NoSync
    (fun _ _ _ prior computed => prior.record computed (by decide)) six attestedOk
  have eight := foldlM_ok_invariant NoSync
    (fun _ _ _ prior computed => prior.record computed (by decide)) seven depositedOk
  have nine := eight.carry (by simpa only [← Array.foldlM_toList] using exitedOk)
  have ten := nine.carry changedOk
  have eleven : NoSync consolidated := by
    split at requestsOk
    · simp only [bind_ok_iff] at requestsOk
      obtain ⟨requested, requestedOk, withdrawn, withdrawnOk, consolidatedOk⟩ := requestsOk
      have first := ten.carry requestedOk
      have second := first.carry withdrawnOk
      exact foldlM_ok_invariant NoSync
        (fun _ _ _ prior computed => prior.record computed (by decide)) second consolidatedOk
    · cases requestsOk
      exact ten
  obtain ⟨credit, debit, _, synced, events⟩ := recordBalance_single syncOk
  refine ⟨consolidated.1, consolidated.2, _, credit, debit, events,
    fun i => ?_, fun i => ?_, synced⟩
  · exact List.sum_eq_zero fun x member => by
      obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
      simp [PinDrift.Internal.syncDebit, eleven e inside]
  · exact List.sum_eq_zero fun x member => by
      obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
      simp [PinDrift.Internal.syncCredit, eleven e inside]

/-- The movement of two sets of keys from one state to another.

The first set counts its debits, and the second counts its credits and its debits. -/
private def moved {fork : Fork} (a b : BeaconState preset fork) (debited moving : Finset ℕ) : ℕ :=
  ∑ i ∈ debited, (actualBalanceAt ⟨fork, a⟩ i - actualBalanceAt ⟨fork, b⟩ i) +
    ∑ i ∈ moving, ((actualBalanceAt ⟨fork, b⟩ i - actualBalanceAt ⟨fork, a⟩ i) +
      (actualBalanceAt ⟨fork, a⟩ i - actualBalanceAt ⟨fork, b⟩ i))

/-- A sync reward step moves two apart sets at most one reward.

The proposer must not be in the second set.

Only the member's balance moves by the reward, and the proposer's share goes outside that set.

The first set holds debits only, which the share does not touch. -/
private theorem applySyncReward_moved_le {fork : Fork} {s t : BeaconState preset fork}
    {reward proposerReward : Gwei} {proposer : Except AccessorError ValidatorIndex}
    {member : ValidatorIndex × Bool} {debited moving : Finset ℕ}
    (apartSets : Disjoint debited moving)
    (apart : ∀ p, proposer = .ok p → p.toNat ∉ moving)
    (ok : applySyncReward reward proposerReward proposer s member = .ok t) :
    moved s t debited moving ≤ reward.toNat := by
  have single
      (le₁ : ∀ i ∈ debited, actualBalanceAt ⟨fork, s⟩ i - actualBalanceAt ⟨fork, t⟩ i ≤
        if member.1.toNat = i then reward.toNat else 0)
      (le₂ : ∀ i ∈ moving, (actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i) +
        (actualBalanceAt ⟨fork, s⟩ i - actualBalanceAt ⟨fork, t⟩ i) ≤
        if member.1.toNat = i then reward.toNat else 0) :
      moved s t debited moving ≤ reward.toNat := by
    unfold moved
    refine (Nat.add_le_add (Finset.sum_le_sum le₁) (Finset.sum_le_sum le₂)).trans ?_
    rw [← Finset.sum_union apartSets, Finset.sum_ite_eq]
    split <;> omega
  unfold applySyncReward at ok
  split at ok
  · simp only [liftAccessor_ok, bind_ok_iff] at ok
    obtain ⟨u, first, p, pOk, last⟩ := ok
    have raised (i : ℕ) := actualBalanceAt_increaseBalance first i
    have paid (i : ℕ) := actualBalanceAt_increaseBalance last i
    refine single (fun i _ => ?_) fun i hi => ?_
    · rw [paid, raised]
      omega
    · have apartAt : p.toNat ≠ i := fun same => apart p pOk (same ▸ hi)
      have paidAt := paid i
      simp only [apartAt, ↓reduceIte, Nat.add_zero] at paidAt
      rw [paidAt, raised]
      split <;> omega
  · have lowered (i : ℕ) := actualBalanceAt_decreaseBalance (liftAccessor_ok.mp ok) i
    refine single (fun i _ => ?_) fun i _ => ?_ <;> rw [lowered] <;> split <;> omega

/-- A sync aggregate moves two apart sets at most one reward for each seat.

The proposer must not be in the second set. -/
private theorem processSyncAggregate_moved_le {fork : Fork} {s t : BeaconState preset fork}
    (altair : .altair ≤ fork) (aggregate : SyncAggregate preset)
    (ok : processSyncAggregate config checks s altair aggregate = .ok t)
    {debited moving : Finset ℕ} (apartSets : Disjoint debited moving)
    (apart : ∀ p, getBeaconProposerIndex s = .ok p → p.toNat ∉ moving) :
    ∃ reward, syncParticipantReward s = .ok reward ∧
      moved s t debited moving ≤ preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat := by
  simp only [processSyncAggregate, bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, reward, rewardOk, proposer, proposerOk,
    members, membersOk, folded⟩ := ok
  refine ⟨reward, rewardOk, ?_⟩
  have fold (xs : List (ValidatorIndex × Bool)) (a b : BeaconState preset fork)
      (ok : xs.foldlM (applySyncReward reward proposer (getBeaconProposerIndex s)) a = .ok b) :
      moved a b debited moving ≤ xs.length * reward.toNat := by
    induction xs generalizing a with
    | nil => cases ok; simp [moved]
    | cons x xs ih =>
      obtain ⟨u, one, rest⟩ := bind_ok_iff.mp ok
      have step := applySyncReward_moved_le apartSets apart one
      have tail := ih u rest
      have triangle : moved a b debited moving ≤ moved a u debited moving +
          moved u b debited moving := by
        unfold moved
        rw [Nat.add_add_add_comm, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Nat.add_le_add (Finset.sum_le_sum fun i _ => by omega)
          (Finset.sum_le_sum fun i _ => by omega)
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  have bounds := fold _ s t (by simpa only [← Array.foldlM_toList] using folded)
  have length : (members.zip aggregate.syncCommitteeBits.bits.toArray).toList.length ≤
      preset.SYNC_COMMITTEE_SIZE.toNat := by
    simp only [Array.length_toList, Array.size_zip]
    exact (Nat.min_le_right _ _).trans (by simp)
  exact bounds.trans (Nat.mul_le_mul_right _ length)

/-- The sync debits of a set of keys and the sync credits and debits of a second set of keys. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.syncSeatMoves (debited moving : Finset
  ℕ) (events : List (BalanceEvent preset)) : ℕ :=
  ∑ i ∈ debited, (events.map (PinDrift.Internal.syncDebit i)).sum +
    ∑ i ∈ moving, ((events.map (PinDrift.Internal.syncCredit i)).sum + (events.map
      (PinDrift.Internal.syncDebit i)).sum)

/-- The movements of two sets of keys add up over the events of two replays. -/
private theorem syncSeatMoves_append (debited moving : Finset ℕ)
    (first second : List (BalanceEvent preset)) :
    PinDrift.Internal.syncSeatMoves debited moving (first ++ second) =
      PinDrift.Internal.syncSeatMoves debited moving first + PinDrift.Internal.syncSeatMoves debited
        moving second := by
  unfold PinDrift.Internal.syncSeatMoves
  simp only [List.map_append, List.sum_append, Finset.sum_add_distrib]
  omega

/-- The sync debits of a block over any keys fit the participant reward of the block's total.

The sync pass is the last pass of the replay, and no other pass records a sync event.

It reads the total of the state after the block, since a sync aggregate changes only balances.

If the block's proposer is not among the keys, they move at most one participant reward per seat. -/
private theorem block_syncDebits_le {fork : Fork} {a t : BeaconState preset fork}
    (early : fork < .glamsterdam) (altair : .altair ≤ fork) {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork} {events : List (BalanceEvent preset)}
    (replay : blockBalanceReplay (config := config) (checks := checks) early engine a block =
      .ok (t, events))
    (total : ℕ) (band : ∀ T : Gwei, getTotalActiveBalance t = .ok T → 2 * T.toNat ≤ 3 * total)
    (keys : Finset ℕ) :
    ∑ i ∈ keys, (events.map (PinDrift.Internal.syncDebit i)).sum ≤
      preset.SYNC_COMMITTEE_SIZE.toNat * PinTerms.syncEnvelope preset total ∧
    ∑ i ∈ keys, ((events.map (PinDrift.Internal.syncCredit i)).sum + (events.map
      (PinDrift.Internal.syncDebit i)).sum) ≤
      preset.SYNC_COMMITTEE_SIZE.toNat * PinDrift.Internal.syncSeatEnvelope preset total ∧
    (∀ debited moving : Finset ℕ, Disjoint debited moving →
      (∀ p, getBeaconProposerIndex t = .ok p → p.toNat ∉ moving) →
      PinDrift.Internal.syncSeatMoves debited moving events ≤
        preset.SYNC_COMMITTEE_SIZE.toNat * PinTerms.syncEnvelope preset total) := by
  obtain ⟨c, rest, aggregate, credit, debit, rfl, silent, silentCredit, synced⟩ :=
    blockReplay_sync_split early altair replay
  obtain ⟨reward, proposer, rewardOk, proposerOk, -, debits, moves⟩ :=
    sync_bounds_combined altair _ synced
  have bound := (DirectSafety.Apriori.Internal.keys_debits_le keys
    ⟨.sync, ⟨fork, c⟩, ⟨fork, t⟩, 0, 0⟩).trans debits
  have movesBound : ∑ i ∈ keys,
      ((actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, c⟩ i) +
        (actualBalanceAt ⟨fork, c⟩ i - actualBalanceAt ⟨fork, t⟩ i)) ≤
        preset.SYNC_COMMITTEE_SIZE.toNat * (reward.toNat + proposer.toNat) := by
    rw [Finset.sum_add_distrib]
    exact (Nat.add_le_add (PinDrift.Internal.keys_credits_le keys ⟨.sync, ⟨fork, c⟩, ⟨fork, t⟩, 0,
      0⟩)
      (DirectSafety.Apriori.Internal.keys_debits_le keys
        ⟨.sync, ⟨fork, c⟩, ⟨fork, t⟩, 0, 0⟩)).trans moves
  obtain ⟨balances, rfl⟩ := processSyncAggregate_eq synced
  have reads := rewardOk
  simp only [syncParticipantReward, bind_ok_iff, liftAccessor_ok] at reads
  obtain ⟨T, totalEnd, -⟩ := reads
  have envelope := syncReward_le_envelope rewardOk totalEnd total (band T totalEnd)
  have share := syncProposer_le envelope proposerOk
  refine ⟨?_, ?_, fun debited moving apartSets apart => ?_⟩
  · simp only [List.map_append, List.sum_append, silent, PinDrift.Internal.syncDebit, ↓reduceIte,
    List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Nat.zero_add, Nat.add_zero]
    exact bound.trans (Nat.mul_le_mul_left _ envelope)
  · simp only [List.map_append, List.sum_append, silent, silentCredit, PinDrift.Internal.syncDebit,
    PinDrift.Internal.syncCredit,
      ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.zero_add,
      Nat.add_zero]
    refine movesBound.trans (Nat.mul_le_mul_left _ ?_)
    unfold PinDrift.Internal.syncSeatEnvelope
    omega
  · -- The proposer is read from the slot and the lookahead, which the sync pass leaves alone.
    have same : getBeaconProposerIndex ({ c with balances } : BeaconState preset fork) =
        getBeaconProposerIndex c := by
      rfl
    obtain ⟨reward', rewardOk', moves'⟩ := processSyncAggregate_moved_le altair _ synced
      apartSets fun p found => apart p (same.trans found)
    obtain rfl : reward' = reward := Except.ok.inj (rewardOk'.symm.trans rewardOk)
    unfold PinDrift.Internal.syncSeatMoves
    simp only [List.map_append, List.sum_append, silent, silentCredit, PinDrift.Internal.syncDebit,
      PinDrift.Internal.syncCredit,
      ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.zero_add,
      Nat.add_zero]
    exact moves'.trans (Nat.mul_le_mul_left _ envelope)

/-- The rewards passes keep the replay free of sync events. -/
private theorem replayRewards_noSync {fork : Fork} {p q : BalanceReplay preset fork}
    (held : NoSync p) (ok : replayRewards (config := config) p = .ok q) : NoSync q :=
  replayRewards_induction NoSync (fun prior ok => prior.record ok (by decide))
    (fun penalty prior ok => prior.record ok (by rcases penalty with rfl | rfl <;> decide)) held ok

/-- No stage of an epoch before the payments records a sync pass. -/
private theorem replay_stage_noSync {fork : Fork} {k : EpochStage}
    (member : k ∈ EpochStage.prefixStages) {p q : BalanceReplay preset fork}
    (ok : epochReplayAction (config := config) (checks := checks) k p = .ok q) :
    NoSync p → NoSync q := by
  intro held
  simp only [EpochStage.prefixStages, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [epochReplayAction] at ok
    exact held.carry ok
  · simp only [epochReplayAction] at ok
    split at ok
    · exact held.carry ok
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      subst ok
      exact held
  · simp only [epochReplayAction] at ok
    exact replayRewards_noSync held ok
  · simp only [epochReplayAction] at ok
    exact held.carry ok
  · simp only [epochReplayAction] at ok
    exact held.record ok (by decide)
  · simp only [epochReplayAction] at ok
    split at ok
    · exact held.carry ok
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      subst ok
      exact held
  -- The pending deposits and the pending consolidations each append one event of their source.
  all_goals
    simp only [epochReplayAction] at ok
    split at ok
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨_, _, rfl⟩ := ok
      intro e member
      rcases List.mem_append.mp member with old | added
      · exact held e old
      · rw [List.mem_singleton.mp added]
        exact nofun
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      subst ok
      exact held

/-- From Electra, a slot step records no sync pass. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.slot_noSync {x y :
  ForkedBeaconState preset} (electra : .pectra ≤ x.fork)
    (ok : advanceSlotAcross config checks x = .ok y) (early : y.fork < .glamsterdam)
    {events : List (BalanceEvent preset)}
    (replayed : (Step.slot ok : Step config checks x y).balanceEvents = .ok events) :
    ∀ e ∈ events, e.source ≠ .sync := by
  obtain ⟨advanced, cached, crossings, advanceOk, upgrades, cachedOk, crossingOk, branch⟩ :=
    Step.balanceEvents_slot ok early replayed
  have noCrossings : crossings = [] :=
    DirectSafety.Apriori.Internal.upgradeBalanceReplay_electra_nil
      (u := ⟨x.fork, advanced⟩) electra crossingOk
  rcases branch with ⟨_, eventsEq⟩ | ⟨middle, updated, recorded, recordOk, _, _, _, eventsEq, _⟩
  · rw [eventsEq, noCrossings]
    intro e member
    cases member
  · rw [eventsEq, noCrossings, List.append_nil]
    have trace := epochBalanceReplay_trace recordOk
    have quiet := trace.transport (fun p q => NoSync p → NoSync q) (fun _ held => held)
      (fun one two held => two (one held))
      (fun _ member _ _ computed => replay_stage_noSync member computed)
    exact quiet (fun _ member => by cases member)

/-- The sync movements of a replay over a set of keys add up over the events of two replays. -/
private theorem sum_syncMoves_append (keys : Finset ℕ) (first second : List (BalanceEvent preset)) :
    ∑ i ∈ keys, (((first ++ second).map (PinDrift.Internal.syncCredit i)).sum +
      ((first ++ second).map (PinDrift.Internal.syncDebit i)).sum) =
    ∑ i ∈ keys, ((first.map (PinDrift.Internal.syncCredit i)).sum + (first.map
      (PinDrift.Internal.syncDebit i)).sum) +
      ∑ i ∈ keys, ((second.map (PinDrift.Internal.syncCredit i)).sum + (second.map
        (PinDrift.Internal.syncDebit i)).sum) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [List.map_append, List.sum_append]
  omega

/-- A slot step neither debits nor credits a key for the sync committee. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.slot_syncDebit_zero {x y :
  ForkedBeaconState preset} (electra : .pectra ≤ x.fork)
    (ok : advanceSlotAcross config checks x = .ok y) (early : y.fork < .glamsterdam)
    {events : List (BalanceEvent preset)}
    (replayed : (Step.slot ok : Step config checks x y).balanceEvents = .ok events) (i : ℕ) :
    (events.map (PinDrift.Internal.syncDebit i)).sum = 0 ∧ (events.map (PinDrift.Internal.syncCredit
      i)).sum = 0 :=
  ⟨List.sum_eq_zero fun v member => by
      obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
      simp [PinDrift.Internal.syncDebit, PinDrift.Internal.slot_noSync electra ok early replayed e
        inside],
    List.sum_eq_zero fun v member => by
      obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
      simp [PinDrift.Internal.syncCredit, PinDrift.Internal.slot_noSync electra ok early replayed e
        inside]⟩

/-- From Electra, a block step records no credit from the deposits source.

In Electra, deposits are credited in the epoch processing, so in slot steps.

A block step only queues deposit requests.

So the deposit events of the step raise no balance, by `blockReplay_unconditional`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.block_deposit_zero {f : Fork} {u w
  : BeaconState preset f}
    {engine : ExecutionEngine preset f} {signed : SignedBeaconBlock preset f}
    {due : upgradeDue config ⟨f, u⟩ = false}
    {ok : applySignedBlock config checks engine u signed true = .ok w}
    {es : List (BalanceEvent preset)} (electra : .pectra ≤ f) (early : f < .glamsterdam)
    (replayed : (Step.block engine signed due ok : Step config checks ⟨f, u⟩ ⟨f, w⟩).balanceEvents =
      .ok es) (i : ℕ) :
    ((es.filter fun e => decide (e.source = .deposits)).map (PinDrift.Internal.keyCredit i)).sum = 0
      := by
  refine List.sum_eq_zero fun c member => ?_
  obtain ⟨e, inFilter, rfl⟩ := List.mem_map.mp member
  obtain ⟨inList, isDeposit⟩ := List.mem_filter.mp inFilter
  have unconditional := PinKeys.blockReplay_unconditional electra early engine u signed.message
    (Step.balanceEvents_block early replayed) e inList (of_decide_eq_true isDeposit) i
  unfold PinDrift.Internal.keyCredit
  omega

/-- A block step is apart from keys if the proposer at its end is not among them.

A slot step is apart from every set of keys. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.stepApart (keys : Finset ℕ) :
    {x y : ForkedBeaconState preset} → Step config checks x y → Prop
  | _, _, .slot _ => True
  | _, y, .block .. => ∀ p, getBeaconProposerIndex y.state = .ok p → p.toNat ∉ keys

/-- The sync debits of a run fit the committee size times the envelope for each block of the run.

The credits and debits together fit one envelope and proposer share for each seat and block. -/
private theorem run_syncDebits_le {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (fulu : .fusaka ≤ x.fork) (early : y.fork < .glamsterdam) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (total : ℕ)
    (band : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → ∀ t : Gwei, getTotalActiveBalance w.state = .ok t →
        2 * t.toNat ≤ 3 * total)
    (keys : Finset ℕ) :
    ∑ i ∈ keys, (events.map (PinDrift.Internal.syncDebit i)).sum ≤
      tail.blockCount * (preset.SYNC_COMMITTEE_SIZE.toNat * PinTerms.syncEnvelope preset total) ∧
    ∑ i ∈ keys, ((events.map (PinDrift.Internal.syncCredit i)).sum + (events.map
      (PinDrift.Internal.syncDebit i)).sum) ≤
      tail.blockCount * (preset.SYNC_COMMITTEE_SIZE.toNat * PinDrift.Internal.syncSeatEnvelope
        preset total) ∧
    (∀ debited moving : Finset ℕ, Disjoint debited moving →
      (∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
        tail.Contains step → PinDrift.Internal.stepApart moving step) →
      PinDrift.Internal.syncSeatMoves debited moving events ≤
        tail.blockCount *
          (preset.SYNC_COMMITTEE_SIZE.toNat * PinTerms.syncEnvelope preset total)) := by
  induction tail generalizing events with
  | nil =>
    simp only [Run.balanceEvents, pure, Except.pure, Except.ok.injEq] at replayed
    subst replayed
    simp [Run.blockCount, PinDrift.Internal.syncSeatMoves]
  | @snoc middle last pre step ih =>
    have earlyMiddle : middle.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have fuluMiddle : .fusaka ≤ middle.fork :=
      Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps)
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    obtain ⟨priorDebits, priorMoves, priorApart⟩ := ih earlyMiddle priorOk
      (fun inner member => band inner (Run.Contains.earlier member step))
    have priorApart' := fun (debited moving : Finset ℕ) (apartSets : Disjoint debited moving)
        (apart : ∀ {u w : ForkedBeaconState preset} (inner : Step config checks u w),
          (pre.snoc step).Contains inner → PinDrift.Internal.stepApart moving inner) =>
      priorApart debited moving apartSets fun inner member =>
        apart inner (Run.Contains.earlier member step)
    split at rest
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
      obtain ⟨added, addedOk, rfl⟩ := rest
      have debitsSplit : ∑ i ∈ keys, ((prior ++ added).map (PinDrift.Internal.syncDebit i)).sum =
          ∑ i ∈ keys, (prior.map (PinDrift.Internal.syncDebit i)).sum +
            ∑ i ∈ keys, (added.map (PinDrift.Internal.syncDebit i)).sum := by
        simp only [List.map_append, List.sum_append, Finset.sum_add_distrib]
      rw [debitsSplit, sum_syncMoves_append]
      cases step with
      | slot ok =>
        have zero := PinDrift.Internal.slot_syncDebit_zero (Nat.le_trans (by decide) fuluMiddle) ok
          early addedOk
        have none : ∀ debited moving : Finset ℕ, PinDrift.Internal.syncSeatMoves debited moving
          added = 0 := by
          intro debited moving
          unfold PinDrift.Internal.syncSeatMoves
          simp [fun i => (zero i).1, fun i => (zero i).2]
        refine ⟨?_, ?_, fun debited moving apartSets apart => ?_⟩
        · simpa [fun i => (zero i).1, fun i => (zero i).2, Run.blockCount] using priorDebits
        · simpa [fun i => (zero i).1, fun i => (zero i).2, Run.blockCount] using priorMoves
        · rw [syncSeatMoves_append, none]
          simpa [Run.blockCount] using priorApart' debited moving apartSets apart
      | @block fork before after engine signed due ok =>
        have altair : Fork.altair ≤ fork :=
          Nat.le_trans (show Fork.altair ≤ Fork.fusaka by decide) fuluMiddle
        have replay := Step.balanceEvents_block early addedOk
        obtain ⟨bound, boundMoves, boundApart⟩ := block_syncDebits_le early altair replay total
          (fun T hT => band _ (Run.Contains.last pre _) T hT) keys
        simp only [Run.blockCount, Nat.add_mul, Nat.one_mul]
        refine ⟨by omega, by omega, fun debited moving apartSets apart => ?_⟩
        have here := boundApart debited moving apartSets (apart _ (Run.Contains.last pre _))
        have before := priorApart' debited moving apartSets apart
        rw [syncSeatMoves_append]
        omega
    · simp only [pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      cases step with
      | slot ok =>
        simpa [Run.blockCount] using And.intro priorDebits (And.intro priorMoves priorApart')
      | block =>
        exact ⟨priorDebits.trans (Nat.mul_le_mul_right _ (Nat.le_succ _)),
          priorMoves.trans (Nat.mul_le_mul_right _ (Nat.le_succ _)),
          fun debited moving apartSets apart => (priorApart' debited moving apartSets apart).trans
            (Nat.mul_le_mul_right _ (Nat.le_succ _))⟩

/-- The blocks of a run fit one amount per seat for each slot of the epochs that the run touches.

The run has at most one block for each slot that it covers. -/
private theorem Run.blockCount_mul_le {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (amount : ℕ)
    (zero : preset.SLOTS_PER_EPOCH.toNat = 0 → amount = 0) :
    tail.blockCount * (preset.SYNC_COMMITTEE_SIZE.toNat * amount) ≤
      ((getCurrentEpoch y.state).toNat + 1 - (getCurrentEpoch x.state).toNat) *
        preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * amount := by
  by_cases empty : preset.SLOTS_PER_EPOCH.toNat = 0
  · simp [zero empty]
  calc tail.blockCount * (preset.SYNC_COMMITTEE_SIZE.toNat * amount)
      ≤ (((getCurrentEpoch y.state).toNat + 1 - (getCurrentEpoch x.state).toNat) *
        preset.SLOTS_PER_EPOCH.toNat) * (preset.SYNC_COMMITTEE_SIZE.toNat * amount) :=
        Nat.mul_le_mul_right _ (Run.blockCount_le_epochs tail (Nat.pos_of_ne_zero empty))
    _ = _ := by ring

/-- The sync debits of any set of keys over a run from Fulu fit one envelope per seat per slot.

The slots are those of the epochs that the run touches.

Every total along the run is within three halves of `total`.

Each block debits the keys at most one participant reward per seat.

Each block moves the keys at most one participant reward and its proposer share per seat.

If no block's proposer is among the keys, each block moves them at most one participant reward.

That reward is per seat. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Run.syncDebits_le {x y :
  ForkedBeaconState preset} (tail : Run config checks x y)
    (fulu : .fusaka ≤ x.fork) (early : y.fork < .glamsterdam) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (total : ℕ)
    (band : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → ∀ t : Gwei, getTotalActiveBalance w.state = .ok t →
        2 * t.toNat ≤ 3 * total)
    (keys : Finset ℕ) :
    ∑ i ∈ keys, (events.map (PinDrift.Internal.syncDebit i)).sum ≤
      ((getCurrentEpoch y.state).toNat + 1 - (getCurrentEpoch x.state).toNat) *
        preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
          PinTerms.syncEnvelope preset total ∧
    ∑ i ∈ keys, ((events.map (PinDrift.Internal.syncCredit i)).sum + (events.map
      (PinDrift.Internal.syncDebit i)).sum) ≤
      ((getCurrentEpoch y.state).toNat + 1 - (getCurrentEpoch x.state).toNat) *
        preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
          PinDrift.Internal.syncSeatEnvelope preset total ∧
    (∀ debited moving : Finset ℕ, Disjoint debited moving →
      (∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
        tail.Contains step → PinDrift.Internal.stepApart moving step) →
      PinDrift.Internal.syncSeatMoves debited moving events ≤
        ((getCurrentEpoch y.state).toNat + 1 - (getCurrentEpoch x.state).toNat) *
          preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
            PinTerms.syncEnvelope preset total) := by
  have empty : preset.SLOTS_PER_EPOCH.toNat = 0 → PinTerms.syncEnvelope preset total = 0 :=
      fun empty => by
    unfold PinTerms.syncEnvelope
    rw [empty]
    simp
  have bounds := run_syncDebits_le tail fulu early high replayed total band keys
  exact ⟨bounds.1.trans (Run.blockCount_mul_le tail _ empty),
    bounds.2.1.trans (Run.blockCount_mul_le tail _ fun e => by
      unfold PinDrift.Internal.syncSeatEnvelope
      simp [empty e]),
    fun debited moving apartSets apart =>
      (bounds.2.2 debited moving apartSets apart).trans (Run.blockCount_mul_le tail _ empty)⟩

end PinSeatDebits

end

section

/-! ## PinSlashFloor -/

namespace PinSlashFloor

open Base Uint64 Models DirectSafety DirectSafety.Apriori.Internal

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- Every fork from Fulu on has the slashing quotient of Electra. -/
private theorem mspq_fusaka {f : Fork} (h : .fusaka ≤ f) :
    (EthLib.Consensus.parameters preset f).MIN_SLASHING_PENALTY_QUOTIENT =
      (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT := by
  have pectra : .pectra ≤ f := Nat.le_trans (by decide) h
  have pectra' : .pectra ≤ Fork.fusaka := by decide
  simp [EthLib.Consensus.parameters, ge_iff_le, pectra, pectra']


/-- Epochs cannot decrease, so a step inside a same-epoch run starts in that epoch. -/
private theorem step_start_epoch_eq {m n a b : ForkedBeaconState preset}
    (r : Run config checks m n) (same : getCurrentEpoch n.state = getCurrentEpoch m.state)
    (step : Step config checks a b) (member : r.Contains step) :
    getCurrentEpoch a.state = getCurrentEpoch m.state := by
  obtain ⟨before, after, -⟩ := r.contains_split step member
  exact UInt64.le_antisymm
    (same ▸ currentEpoch_le_of_chainSteps ((Run.nil.snoc step).append after).chainSteps)
    (currentEpoch_le_of_chainSteps before.chainSteps)

/-- A final step can cross the boundary, but it still starts in the prefix's epoch. -/
private theorem snoc_step_start_epoch_eq {m z n a b : ForkedBeaconState preset}
    (pre : Run config checks m z) (last : Step config checks z n)
    (same : getCurrentEpoch z.state = getCurrentEpoch m.state)
    (step : Step config checks a b) (member : (pre.snoc last).Contains step) :
    getCurrentEpoch a.state = getCurrentEpoch m.state := by
  cases member with
  | last => exact same
  | earlier member _ => exact step_start_epoch_eq pre same step member

open Classical in
/-- The rewards pass at the last state of the first epoch debits a key at most its pass rate.

The run stays in the epoch of `m` up to `z`, and the slot step `ok` leaves it.

The pass is a debit only when it reads a total active balance at `z`.

Otherwise it records no penalty. -/
private theorem lastPass_debit_le {m z n : ForkedBeaconState preset} (pre : Run config checks m z)
    (ok : advanceSlotAcross config checks z = .ok n) (altair : .altair ≤ m.fork)
    (early : n.fork < .glamsterdam) (same : getCurrentEpoch z.state = getCurrentEpoch m.state)
    (crossed : (getCurrentEpoch z.state).toNat < (getCurrentEpoch n.state).toNat)
    (endEpoch : (getCurrentEpoch n.state).toNat ≤ (getCurrentEpoch m.state).toNat + 1)
    {i : ℕ} (inside : i < m.state.validators.data.size) {events : List (BalanceEvent preset)}
    (replayed : (pre.snoc (Step.slot ok)).balanceEvents (getCurrentEpoch m.state).toNat =
      .ok events) :
    (events.map (penaltyDebit i)).sum ≤
      if ∃ total, getTotalActiveBalance z.state = .ok total then PinDrift.Internal.passPenaltyRate
        config z i
      else 0 := by
  have bound := PinDrift.Internal.segment_passDebit_le_guarded (pre.snoc (Step.slot ok)) early
    altair
    (getCurrentEpoch m.state).toNat endEpoch
    (snoc_step_start_epoch_eq pre (Step.slot ok) same) inside
    (if ∃ total, getTotalActiveBalance z.state = .ok total then PinDrift.Internal.passPenaltyRate
      config z i
      else 0)
    (fun {z'} pre' ok' split before found => by
      obtain ⟨total, -, totalOk, -⟩ := found
      have hasTotal : ∃ total, getTotalActiveBalance z'.state = .ok total := ⟨total, totalOk⟩
      cases split
      simp [hasTotal])
    replayed
  rwa [ite_eq_left (by rw [same] at crossed; exact UInt64.lt_iff_toNat_lt.mpr crossed)] at bound

open Classical in
/-- The floor of one key over a run that crosses at most one epoch boundary.

The run starts at `m`, reached from genesis, and ends at `n`, from Fulu and before Gloas.

It stays in the epoch of `m`.

Or it ends with the slot step that leaves that epoch, at the first slot of the next epoch.

The key must be assigned an activation at `m`, and not exit by the epoch after that of `m`.

If it is slashed at `m`, its delayed slashing penalty must not be due by the epoch of `n`.

Take any `C` below the key's largest effective balance at `m`.

The least of the balance at `m` and `C` is at most the balance at `n`, plus its debits.

The first debit is the pass at the last state `z` of the first epoch, if the run crosses its end.

The pass is a debit only when it reads a total active balance there.

Otherwise it records no penalty.

The others are the key's sync debits and its payments from the queue of partial withdrawals.

The last is its initial slashing penalty, if the run slashes it.

That penalty is the effective balance at `m` over the slashing quotient.

The effective balance changes only at the boundary, after any slashing before it. -/
private theorem epochFloor {g m n : ForkedBeaconState preset} (shared : Run config checks g m)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (vector : 4 ≤ preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat)
    (positive :
      0 < (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat)
    (r : Run config checks m n) (hm : .fusaka ≤ m.fork) (hn : n.fork < .glamsterdam)
    (shape : getCurrentEpoch n.state = getCurrentEpoch m.state ∨
      ∃ (z : ForkedBeaconState preset) (pre : Run config checks m z)
        (ok : advanceSlotAcross config checks z = .ok n),
        r = pre.snoc (Step.slot ok) ∧ getCurrentEpoch z.state = getCurrentEpoch m.state ∧
          (getCurrentEpoch n.state).toNat = (getCurrentEpoch m.state).toNat + 1)
    (i : ℕ) (val : Validator) (hval : m.state.validators.data[i]? = some val)
    (hact : val.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (hexit : ∀ w, n.state.validators.data[i]? = some w →
      (getCurrentEpoch m.state).toNat + 1 < w.exitEpoch.toNat)
    (hslash : val.slashed = true → (getCurrentEpoch n.state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 < val.withdrawableEpoch.toNat)
    (C : ℕ) (hC : C ≤ (withdrawalMaxEffectiveBalance preset m.fork val).toNat)
    {events : List (BalanceEvent preset)}
    (replayed : r.balanceEvents (getCurrentEpoch m.state).toNat = .ok events) :
    ∃ (z : ForkedBeaconState preset) (pre : Run config checks m z) (post : Run config checks z n),
      r = pre.append post ∧ getCurrentEpoch z.state = getCurrentEpoch m.state ∧
      min (actualBalanceAt m i) C ≤ actualBalanceAt n i +
        (if getCurrentEpoch m.state < getCurrentEpoch n.state ∧
            ∃ total, getTotalActiveBalance z.state = .ok total then
          PinDrift.Internal.passPenaltyRate config z i else 0) +
        (events.map (PinDrift.Internal.syncDebit i)).sum + (events.map (floorPartialDebit
          i.toUInt64)).sum +
        (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
          then effectiveAt m i /
            (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat
          else 0) := by
  have mEarly : m.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps r.chainSteps) hn
  have inside : i < m.state.validators.data.size := (Array.getElem?_eq_some_iff.mp hval).1
  obtain ⟨iv, rfl⟩ : ∃ iv : ValidatorIndex, iv.toNat = i :=
    ⟨i.toUInt64, toNat_toUInt64_of_lt (m.state.validators.bound mEarly) inside⟩
  have altair : .altair ≤ m.fork := Nat.le_trans (by decide) hm
  have mn : (getCurrentEpoch m.state).toNat ≤ (getCurrentEpoch n.state).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps r.chainSteps)
  have endEpoch : (getCurrentEpoch n.state).toNat ≤ (getCurrentEpoch m.state).toNat + 1 := by
    rcases shape with same | ⟨z, pre, ok, req, hz, h1⟩
    · rw [same]; omega
    · omega
  -- Every step of the run starts in the epoch of `m`, at a fork from Fulu.
  have starts : ∀ {a b : ForkedBeaconState preset} (pre' : Run config checks m a)
      (step : Step config checks a b) (post : Run config checks b n),
      (pre'.snoc step).append post = r → getCurrentEpoch a.state = getCurrentEpoch m.state ∧
        .fusaka ≤ a.fork ∧ b.fork < .glamsterdam := by
    intro a b pre' step post split
    have forkLo := fork_le_of_chainSteps pre'.chainSteps
    have forkHi := fork_le_of_chainSteps post.chainSteps
    refine ⟨?_, Nat.le_trans hm forkLo, Nat.lt_of_le_of_lt forkHi hn⟩
    have member : r.Contains step := by
      rw [← split, Run.contains_append]
      exact .inl (.last _ _)
    rcases shape with same | ⟨z, pre, ok, req, hz, h1⟩
    · exact step_start_epoch_eq r same step member
    · exact snoc_step_start_epoch_eq pre (Step.slot ok) hz step (req ▸ member)
  obtain ⟨z, pre, post, hsplit, hz, hpen⟩ : ∃ (z : ForkedBeaconState preset)
      (pre : Run config checks m z) (post : Run config checks z n),
      r = pre.append post ∧ getCurrentEpoch z.state = getCurrentEpoch m.state ∧
      (events.map (penaltyDebit iv.toNat)).sum ≤
        (if getCurrentEpoch m.state < getCurrentEpoch n.state ∧
            ∃ total, getTotalActiveBalance z.state = .ok total then
          PinDrift.Internal.passPenaltyRate config z iv.toNat else 0) := by
    rcases shape with same | ⟨z, pre, ok, req, hz, h1⟩
    · refine ⟨n, r, .nil, rfl, same, ?_⟩
      have free := (epoch_sync_data r altair hn same _ replayed).2.1
      have quiet : ¬ (getCurrentEpoch m.state < getCurrentEpoch n.state ∧
          ∃ total, getTotalActiveBalance n.state = .ok total) := fun h =>
        absurd h.1 (by simp [same])
      simp only [quiet, ↓reduceIte]
      exact Nat.le_of_eq (List.sum_eq_zero fun _ member => by
        obtain ⟨e, present, rfl⟩ := List.mem_map.mp member
        simp [penaltyDebit, (free e present).1, (free e present).2])
    · subst req
      refine ⟨z, pre, Run.nil.snoc (Step.slot ok), rfl, hz, ?_⟩
      have crossed : getCurrentEpoch m.state < getCurrentEpoch n.state :=
        UInt64.lt_iff_toNat_lt.mpr (by omega)
      have hzn : (getCurrentEpoch z.state).toNat = (getCurrentEpoch m.state).toNat := by rw [hz]
      have bound := lastPass_debit_le pre ok altair hn hz (by omega) endEpoch inside replayed
      by_cases found : ∃ total, getTotalActiveBalance z.state = .ok total
      · simpa [crossed, found] using bound
      · simpa [found] using bound
  refine ⟨z, pre, post, hsplit, hz, ?_⟩
  have effEq : ∀ {a b : ForkedBeaconState preset} (pre' : Run config checks m a)
      (step : Step config checks a b) (post' : Run config checks b n),
      (pre'.snoc step).append post' = r → effectiveAt a iv.toNat = effectiveAt m iv.toNat := by
    intro a b pre' step post' split
    obtain ⟨epoch, -, bEarly⟩ := starts pre' step post' split
    have aEarly : a.fork < .glamsterdam := Nat.lt_of_le_of_lt step.chainStep.fork_le bEarly
    exact run_same_epoch_effective pre' aEarly epoch iv.toNat inside
  have positive' :
      0 < (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat := by
    rw [mspq_fusaka hm]; exact positive
  have half : (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat =
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 := by simp
  obtain ⟨last, trace, balance, debt, -, w, final, -, used, -, bounded, startSlashed⟩ :=
    FloorTrace.run_of_le_cap_general shared r genesis caps delay hn
      (getCurrentEpoch m.state).toNat endEpoch iv val hval (Or.inl hact)
      (min (actualBalanceAt m iv.toNat) C) (effectiveAt m iv.toNat)
      (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat
      (Nat.le_trans (Nat.min_le_right _ _) hC) positive'
      (fun {a b} pre' step post' split w found => by
        obtain ⟨epoch, fusaka, bEarly⟩ := starts pre' step post' split
        have epochs : (getCurrentEpoch a.state).toNat = (getCurrentEpoch m.state).toNat := by
          rw [epoch]
        have atMost := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps
          ((Run.nil.snoc step).append post').chainSteps)
        have inv := Run.invariant genesis.invariant (shared.append pre')
        refine ⟨Or.inl ?_, ⟨fun _ => by omega, fun slashed => ?_⟩, ?_,
          fun evs hevs e member crossing => ?_⟩
        · obtain ⟨w', found', life⟩ := post'.registryLifecycle.validators iv.toNat w found
          have kept := hexit w' found'
          have small := w'.exitEpoch.toNat_lt
          by_cases assigned : w.exitEpoch = FAR_FUTURE_EPOCH
          · rw [assigned]
            simp [FAR_FUTURE_EPOCH]
            omega
          · rw [← life.exitEpoch assigned]; exact kept
        · have := hslash slashed
          omega
        · rw [mspq_fusaka hm, mspq_fusaka fusaka]
        · have sites := (step.balanceEvents_sites bEarly inv caps.compounding hevs) e member
          obtain ⟨before, -⟩ := sites.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 crossing
          exact Nat.not_le_of_lt before (Nat.le_trans (by decide) fusaka))
      replayed
  obtain ⟨-, slashBound⟩ := bounded (effectiveAt m iv.toNat) le_rfl
    (fun pre' step post' split => (effEq pre' step post' split).le)
  have floor := FloorTrace.balance_floor_general trace
    (by simp)
  have split : (events.map (floorPenaltyDebit iv.toNat)).sum =
      (events.map (penaltyDebit iv.toNat)).sum + (events.map (PinDrift.Internal.syncDebit
        iv.toNat)).sum := by
    rw [← List.sum_map_add]
    rfl
  have index : iv.toNat.toUInt64 = iv := by simp
  rw [balance, debt, split] at floor
  rw [index]
  cases hs : last.slashedHigh with
  | none =>
    simp only [hs, Option.elim] at floor
    omega
  | some h =>
    have atMost := slashBound h hs
    have slashed : w.slashed = true := by
      cases hw : w.slashed
      · simp [hs, hw] at used
      · rfl
    have unslashed : val.slashed = false := by
      cases hv : val.slashed
      · rfl
      · have := startSlashed hv
        rw [hs] at this
        cases this
    simp only [hs, Option.elim] at floor
    have cond : val.slashed = false ∧ ∃ w, n.state.validators.data[iv.toNat]? = some w ∧
        w.slashed = true := ⟨unslashed, w, final, slashed⟩
    simp only [cond, and_self, ↓reduceIte]
    omega

end PinSlashFloor

end

section

/-! ## The floor path of a new key's effective balance -/

namespace PinKeys

open Base Uint64 Models DirectSafety PinKeyFloor PinSlashFloor

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-! ## A potential that retains a decreasing floor -/

/-- One epoch keeps the fraction of the potential that the floor keeps, up to a rounding error.

The floor `φj` never rises, and stays within three halves of its start `φ0`.

The potential `dj` keeps the fraction `φj1 / φj` of itself, less the error `e`.

Then `d0` keeps the fraction `φj1 / φ0` of itself after `j + 1` epochs.

It loses `3 e (j + 1) / 2` over `φ0`. -/
private theorem chain_step (φ0 φj φj1 d0 dj dj1 e j : ℕ) (pos : 0 < φj) (anti : φj1 ≤ φj)
    (band : 2 * φ0 ≤ 3 * φj) (ih : 2 * d0 * φj ≤ 2 * dj * φ0 + 3 * e * j)
    (step : dj * φj1 ≤ dj1 * φj + e) :
    2 * d0 * φj1 ≤ 2 * dj1 * φ0 + 3 * e * (j + 1) := by
  refine Nat.le_of_mul_le_mul_right ?_ pos
  calc 2 * d0 * φj1 * φj = (2 * d0 * φj) * φj1 := by ring
    _ ≤ (2 * dj * φ0 + 3 * e * j) * φj1 := Nat.mul_le_mul_right _ ih
    _ = 2 * φ0 * (dj * φj1) + 3 * e * j * φj1 := by ring
    _ ≤ 2 * φ0 * (dj1 * φj + e) + 3 * e * j * φj := by
        apply Nat.add_le_add
        · exact Nat.mul_le_mul_left _ step
        · exact Nat.mul_le_mul_left _ anti
    _ = 2 * dj1 * φ0 * φj + 2 * φ0 * e + 3 * e * j * φj := by ring
    _ ≤ 2 * dj1 * φ0 * φj + 3 * φj * e + 3 * e * j * φj := by
        have := Nat.mul_le_mul_right e band
        omega
    _ = (2 * dj1 * φ0 + 3 * e * (j + 1)) * φj := by ring

/-! ## One epoch of a key against the floor path -/

/-- The effective balance `EB` is within the band above the least of the balance and the cap.

The least of the balance and `K` is at most the least of the balance and the cap. -/
private theorem eb_le_min_band (b' cap K band EB : ℕ) (hcap : K ≤ cap)
    (hyst : EB ≤ b' + band) (hcapEB : EB ≤ cap) :
    EB ≤ min b' cap + band ∧ min b' K ≤ min b' cap := by
  refine ⟨?_, min_le_min_left _ hcap⟩
  rcases le_total b' cap with h | h
  · rw [min_eq_left h]
    exact hyst
  · rw [min_eq_right h]
    omega

/-- An epoch that starts at or above `K` keeps the potential, since the floor only falls. -/
private theorem big_arith (c K band X φt φt1 : ℕ) (hc : c ≤ K) (hφ : φt1 ≤ φt) :
    (c + band) * φt1 ≤ (K + band) * φt + (K + band) + X * φt := by
  have := Nat.mul_le_mul (Nat.add_le_add_right hc band) hφ
  nlinarith

/-- One epoch of a key keeps the fraction of its potential that the floor keeps.

The potential is the least of the balance and `K`, plus the downward band.

The epoch loses at most its pass.

The pass is charged at the effective balance `EB`.

That balance lies within the band above the balance, and below the cap.

The pass rate is at most `EB * (pen + 1) / φt`.

Here `φt = φt1 + pen` is the floor before the epoch, and `φt1` the floor after it.

The error is `K + band`, from the rounding. -/
private theorem step_arith (b' b cap K band pass X φt φt1 pen EB : ℕ)
    (hcap : K ≤ cap)
    (seg : min b' cap ≤ b + pass + X)
    (hyst : EB ≤ b' + band) (hcapEB : EB ≤ cap)
    (pr : pass * φt ≤ EB * (pen + 1))
    (ph : φt = φt1 + pen) (hφ : 1 ≤ φt1) :
    (min b' K + band) * φt1 ≤ (min b K + band) * φt + (K + band) + X * φt := by
  obtain ⟨hEB, hcle⟩ := eb_le_min_band b' cap K band EB hcap hyst hcapEB
  set C := min b' cap with hC
  -- the key's balance after the epoch, scaled
  have bound : C * φt ≤ b * φt + (C + band) * (pen + 1) + X * φt := by
    have h1 : C * φt ≤ (b + pass + X) * φt := Nat.mul_le_mul_right _ seg
    have h2 : pass * φt ≤ (C + band) * (pen + 1) :=
      pr.trans (Nat.mul_le_mul_right _ hEB)
    nlinarith
  by_cases big : K ≤ b
  · rw [min_eq_right big]
    exact big_arith _ _ _ _ _ _ (min_le_right _ _) (by omega)
  · have small : b < K := Nat.lt_of_not_ge big
    have : min b K = b := min_eq_left small.le
    rw [this]
    -- c ≤ C, and the bound on C·φt1
    set c := min b' K with hc
    have hcK : c ≤ K := min_le_right _ _
    have key : C * φt ≤ b * φt + (C + band) * (pen + 1) + X * φt := bound
    -- (C + band) * (pen + 1) = (C + band) * pen + (C + band)
    have e1 : (C + band) * (pen + 1) = (C + band) * pen + (C + band) := by ring
    -- C * φt - (C+band) pen = C * φt1 - band * pen
    have e2 : C * φt = C * φt1 + C * pen := by rw [ph]; ring
    have lower : (C + band) * φt1 ≤ (b + band) * φt + (C + band) + X * φt := by
      rw [ph] at key ⊢
      nlinarith
    -- replace C by c: C could exceed K, then use the shape of the loss
    by_cases cK : C ≤ K
    · have hcC : c = C := le_antisymm hcle (le_min (min_le_left _ _) cK)
      rw [hcC]
      have : (C + band) ≤ (K + band) := by omega
      omega
    · have above : K < C := Nat.lt_of_not_ge cK
      have h3 : C * φt1 ≤ b * φt + C + band * (pen + 1) + X * φt := by
        rw [ph] at key
        nlinarith
      have h4 : K * φt1 + C ≤ C * φt1 + K := by
        have : K * (φt1 - 1) ≤ C * (φt1 - 1) := Nat.mul_le_mul_right _ above.le
        have e1 : K * (φt1 - 1) + K = K * φt1 := by
          have := Nat.mul_le_mul_left K hφ
          rw [Nat.mul_sub]; omega
        have e2 : C * (φt1 - 1) + C = C * φt1 := by
          have := Nat.mul_le_mul_left C hφ
          rw [Nat.mul_sub]; omega
        omega
      have h5 : (c + band) * φt1 ≤ (K + band) * φt1 := Nat.mul_le_mul_right _ (by omega)
      rw [ph]
      nlinarith

/-- One epoch of a key, with the initial penalty of a slashing in it.

The penalty is at most `EB / Q`, and the epoch is charged `Bq` for it, with `K + band ≤ Q * Bq`.

The floor after the epoch stays at least `6 Q` and within three halves of the floor before. -/
private theorem step_arith_slash (b' b cap K band pass X sl Q Bq φt φt1 pen EB : ℕ)
    (hcap : K ≤ cap) (hQ : 2 ≤ Q) (hB : K + band ≤ Q * Bq)
    (seg : min b' cap ≤ b + pass + X + sl) (hsl : Q * sl ≤ EB)
    (hyst : EB ≤ b' + band) (hcapEB : EB ≤ cap)
    (pr : pass * φt ≤ EB * (pen + 1))
    (ph : φt = φt1 + pen) (hφ : 6 * Q ≤ φt1) (hband : 2 * φt ≤ 3 * φt1) :
    (min b' K + band) * φt1 ≤
      (min b K + band) * φt + (K + band) + (X + (if sl = 0 then 0 else Bq)) * φt := by
  by_cases noSlash : sl = 0
  · subst noSlash
    simp only [ite_true, Nat.add_zero, Nat.add_zero] at seg ⊢
    have := step_arith b' b cap K band pass X φt φt1 pen EB hcap (by simpa using seg) hyst
      hcapEB pr ph (by omega)
    simpa using this
  · simp only [noSlash, ite_false]
    obtain ⟨hEB, hcle⟩ := eb_le_min_band b' cap K band EB hcap hyst hcapEB
    set C := min b' cap with hC
    by_cases cK : C ≤ K
    · -- the penalty is at most `Bq`, and the case is that without slashing
      have slB : sl ≤ Bq := by
        have : Q * sl ≤ Q * Bq := by omega
        exact Nat.le_of_mul_le_mul_left this (by omega)
      have := step_arith b' b cap K band pass (X + sl) φt φt1 pen EB hcap
        (by omega) hyst hcapEB pr ph (by omega)
      have h2 : (X + sl) * φt ≤ (X + Bq) * φt := Nat.mul_le_mul_right _ (by omega)
      omega
    · have above : K < C := Nat.lt_of_not_ge cK
      by_cases big : K ≤ b
      · rw [min_eq_right big]
        exact big_arith _ _ _ _ _ _ (min_le_right _ _) (by omega)
      · have small : b < K := Nat.lt_of_not_ge big
        have : min b K = b := min_eq_left small.le
        rw [this]
        have hc : min b' K ≤ K := min_le_right _ _
        obtain ⟨h, hh⟩ : ∃ h, Q * φt1 = h + Q + φt := by
          refine ⟨Q * φt1 - Q - φt, ?_⟩
          have : 3 * (Q * φt1) ≥ 2 * Q * φt := by nlinarith
          have : Q * φt1 ≥ Q + φt := by nlinarith
          omega
        have h1 : Q * C * φt ≤ Q * b * φt + Q * (C + band) * (pen + 1) + Q * X * φt +
            (C + band) * φt := by
          have a1 : C * φt ≤ (b + pass + X + sl) * φt := Nat.mul_le_mul_right _ seg
          have a2 : pass * φt ≤ (C + band) * (pen + 1) := pr.trans (Nat.mul_le_mul_right _ hEB)
          have a3 : Q * sl ≤ C + band := hsl.trans hEB
          have a4 : Q * (sl * φt) ≤ (C + band) * φt := by
            rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ a3
          have a5 : Q * (pass * φt) ≤ Q * ((C + band) * (pen + 1)) := Nat.mul_le_mul_left _ a2
          have a6 : Q * (C * φt) ≤ Q * ((b + pass + X + sl) * φt) := Nat.mul_le_mul_left _ a1
          have a7 : Q * ((b + pass + X + sl) * φt) =
              Q * (b * φt) + Q * (pass * φt) + Q * (X * φt) + Q * (sl * φt) := by ring
          have a8 : Q * C * φt = Q * (C * φt) := by ring
          have a9 : Q * b * φt = Q * (b * φt) := by ring
          have a10 : Q * (C + band) * (pen + 1) = Q * ((C + band) * (pen + 1)) := by ring
          have a11 : Q * X * φt = Q * (X * φt) := by ring
          rw [a8, a9, a10, a11]
          omega
        have e1 : Q * C * φt = Q * C * φt1 + Q * C * pen := by rw [ph]; ring
        have e2 : Q * (C + band) * (pen + 1) =
            Q * C * pen + Q * C + Q * band * pen + Q * band := by ring
        have e3 : C * (Q * φt1) = C * h + C * Q + C * φt := by rw [hh]; ring
        have e4 : (C + band) * φt = C * φt + band * φt := by ring
        have hC : C * h ≤ Q * b * φt + Q * band * pen + Q * band + Q * X * φt + band * φt := by
          linarith [h1, e1, e2, e3, e4]
        have h2 : K * h ≤ C * h := Nat.mul_le_mul_right _ above.le
        have e5 : K * (Q * φt1) = K * h + K * Q + K * φt := by rw [hh]; ring
        have e6 : Q * band * φt = Q * band * φt1 + Q * band * pen := by rw [ph]; ring
        have h3 : Q * K * φt1 + Q * band * φt1 ≤
            Q * b * φt + Q * band * φt + Q * (K + band) + Q * X * φt + (K + band) * φt := by
          have e7 : (K + band) * φt = K * φt + band * φt := by ring
          have e8 : Q * (K + band) = Q * K + Q * band := by ring
          linarith [hC, h2, e5, e6, e7, e8]
        have h4 : (K + band) * φt ≤ Q * Bq * φt := Nat.mul_le_mul_right _ hB
        have h5 : (min b' K + band) * φt1 ≤ (K + band) * φt1 := Nat.mul_le_mul_right _ (by omega)
        have h6 : Q * ((K + band) * φt1) ≤
            Q * ((b + band) * φt + (K + band) + (X + Bq) * φt) := by
          have e9 : Q * ((K + band) * φt1) = Q * K * φt1 + Q * band * φt1 := by ring
          have e10 : Q * ((b + band) * φt + (K + band) + (X + Bq) * φt) =
              Q * b * φt + Q * band * φt + Q * (K + band) + Q * X * φt + Q * Bq * φt := by ring
          rw [e9, e10]
          omega
        have h7 := Nat.le_of_mul_le_mul_left h6 (by omega)
        omega

/-! ## The state before a new key is scheduled -/

/-- A key that is activated by the end of a run is scheduled two epochs before its activation.

The key may have exited, so long as its activation is before its exit.

It is not active by the epoch after the start of the run.

At the state `z` that the run reaches in that epoch, the key holds its activation epoch `A`.

Activity up to `A` is fixed at `z`, since the seed lookahead is at least three epochs. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Run.start_state {x y :
  ForkedBeaconState preset} (tail : Run config checks x y)
    (window : preset.SeedLookaheadAtLeastThree) (i : ℕ)
    (pending : ∀ v, x.state.validators.data[i]? = some v →
      (getCurrentEpoch x.state).toNat + 1 < v.activationEpoch.toNat)
    (activated : ∃ vy, y.state.validators.data[i]? = some vy ∧
      vy.activationEpoch ≠ FAR_FUTURE_EPOCH ∧ vy.activationEpoch ≤ getCurrentEpoch y.state)
    (ordered : ∀ vy, y.state.validators.data[i]? = some vy →
      vy.activationEpoch.toNat < vy.exitEpoch.toNat) :
    ∃ (z : ForkedBeaconState preset) (pre : Run config checks x z) (post : Run config checks z y)
      (v0 vy : Validator), tail = pre.append post ∧ z.state.validators.data[i]? = some v0 ∧
      y.state.validators.data[i]? = some vy ∧ v0.activationEpoch = vy.activationEpoch ∧
      (getCurrentEpoch z.state).toNat + 2 = vy.activationEpoch.toNat ∧
      vy.activationEpoch.toNat ≤ (getCurrentEpoch y.state).toNat := by
  obtain ⟨vy, foundY, -, activeY⟩ := activated
  have lowY := UInt64.le_iff_toNat_le.mp activeY
  have highY := ordered vy foundY
  have exitBound := vy.exitEpoch.toNat_lt
  have fixedWindow : 3 ≤ preset.MAX_SEED_LOOKAHEAD.toNat := window
  -- Activity at the epoch `A` of the key, as the end state reads it.
  have activeAtA : isActiveAt y.state vy.activationEpoch i = true := by
    refine isActiveAt_eq_true_iff.mpr ⟨vy, foundY, ?_⟩
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨UInt64.le_refl _, UInt64.lt_iff_toNat_lt.mpr highY⟩
  have kept (h : ForkedBeaconState preset) (run : Run config checks h y)
      (le : vy.activationEpoch.toNat ≤ (getCurrentEpoch h.state).toNat +
        preset.MAX_SEED_LOOKAHEAD.toNat) :
      isActiveAt h.state vy.activationEpoch i = true := by
    have bound : vy.activationEpoch ≤ activityFixedEpoch h.state := by
      rw [UInt64.le_iff_toNat_le, activityFixedEpoch_toNat]
      omega
    rw [← activeKept_of_chainSteps run.chainSteps _ bound]
    exact activeAtA
  -- The key is not active by the epoch after the start of the run.
  have later : (getCurrentEpoch x.state).toNat + 1 < vy.activationEpoch.toNat := by
    by_contra early
    have atX := kept x tail (by omega)
    obtain ⟨vx, foundX, activeX⟩ := isActiveAt_eq_true_iff.mp atX
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at activeX
    have := pending vx foundX
    have := UInt64.le_iff_toNat_le.mp activeX.1
    omega
  have startEpoch := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tail.chainSteps)
  obtain ⟨z, pre, post, epoch, split⟩ :=
    Run.exists_epoch_split tail (vy.activationEpoch.toNat - 2) (by omega) (by omega)
  have atZ := kept z post (by omega)
  obtain ⟨v0, foundZ, activeZ⟩ := isActiveAt_eq_true_iff.mp atZ
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at activeZ
  have assigned : v0.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    intro far
    have := UInt64.le_iff_toNat_le.mp activeZ.1
    rw [far] at this
    have : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    omega
  obtain ⟨w, foundW, life⟩ := post.registryLifecycle.validators i v0 foundZ
  have same : w = vy := Option.some.inj (foundW.symm.trans foundY)
  subst same
  exact ⟨z, pre, post, v0, w, split, foundZ, foundY, (life.activationEpoch assigned).symm,
    by omega, lowY⟩

/-! ## The pass rate against the floor path -/

section FloorPath

open DirectSafety.Apriori

/-- The base-reward part of the pass rate fits the base-reward part of the floor's penalty.

The pass reads the root of a total at least that of the floor.

The floor's penalty is read at a weight at least the floor.

The constants satisfy `a * d + b * d ≤ c * b`, which leaves room for the rounding. -/
private theorem pass_first (a b c d BRF EB φ w s T : ℕ) (hb : 0 < b) (hd : 0 < d) (hs : 0 < s)
    (sT : s ≤ T) (sφ : s ≤ φ) (hw : φ ≤ w) (hBRF : 1 ≤ BRF) (ratio : a * d + b * d ≤ c * b) :
    a * BRF * EB / (b * T) * φ ≤ EB * (c * BRF * w / (d * s)) := by
  set Q1 := a * BRF * EB / (b * T) with hQ1
  set P := c * BRF * w / (d * s) with hP
  have h1 : Q1 * (b * T) ≤ a * BRF * EB := Nat.div_mul_le_self _ _
  have h2 : c * BRF * w < (P + 1) * (d * s) := by
    have := Nat.lt_mul_div_succ (c * BRF * w) (Nat.mul_pos hd hs)
    rw [← hP] at this
    linarith
  have step1 : Q1 * φ * (b * d * s) ≤ a * d * BRF * EB * φ := by
    calc Q1 * φ * (b * d * s) = (Q1 * (b * s)) * φ * d := by ring
      _ ≤ (Q1 * (b * T)) * φ * d := by
          apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ sT)
      _ ≤ (a * BRF * EB) * φ * d := by
          apply Nat.mul_le_mul_right; exact Nat.mul_le_mul_right _ h1
      _ = a * d * BRF * EB * φ := by ring
  have step2 : b * EB * (d * s) ≤ b * d * BRF * EB * φ := by
    have : d * s ≤ d * (BRF * φ) :=
      Nat.mul_le_mul_left _ (sφ.trans (Nat.le_mul_of_pos_left _ hBRF))
    calc b * EB * (d * s) ≤ b * EB * (d * (BRF * φ)) := Nat.mul_le_mul_left _ this
      _ = b * d * BRF * EB * φ := by ring
  have step3 : (a * d + b * d) * BRF * EB * φ ≤ b * EB * (c * BRF * w) := by
    calc (a * d + b * d) * BRF * EB * φ ≤ (c * b) * BRF * EB * φ := by
          apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right
          exact ratio
      _ ≤ (c * b) * BRF * EB * w := Nat.mul_le_mul_left _ hw
      _ = b * EB * (c * BRF * w) := by ring
  have step4 : b * EB * (c * BRF * w) ≤ b * EB * (P * (d * s)) + b * EB * (d * s) := by
    have : c * BRF * w ≤ P * (d * s) + d * s := by linarith
    calc b * EB * (c * BRF * w) ≤ b * EB * (P * (d * s) + d * s) := Nat.mul_le_mul_left _ this
      _ = b * EB * (P * (d * s)) + b * EB * (d * s) := by ring
  have key : Q1 * φ * (b * d * s) ≤ EB * P * (b * d * s) := by
    have e : (a * d + b * d) * BRF * EB * φ = a * d * BRF * EB * φ + b * d * BRF * EB * φ := by ring
    have e2 : b * EB * (P * (d * s)) = EB * P * (b * d * s) := by ring
    omega
  exact Nat.le_of_mul_le_mul_right key (Nat.mul_pos (Nat.mul_pos hb hd) hs)

/-- The leak part of the pass rate fits the leak part of the floor's penalty.

The divisor of the penalty is at most the divisor of the pass.

The score of the pass is at most that of the penalty, and the rounding costs one. -/
private theorem pass_second (bias IPQ IPD EB score S' φ w : ℕ) (hIPD : 0 < IPD)
    (div : IPD ≤ bias * IPQ) (sc : score + bias ≤ S') (hw : φ ≤ w) :
    EB * (score + bias) / (bias * IPQ) * φ ≤ EB * (w * S' / IPD + 1) := by
  set Q2 := EB * (score + bias) / (bias * IPQ) with hQ2
  set R := w * S' / IPD with hR
  have h0 : Q2 ≤ EB * (score + bias) / IPD := Nat.div_le_div_left div hIPD
  have h1 : (EB * (score + bias) / IPD) * IPD ≤ EB * (score + bias) := Nat.div_mul_le_self _ _
  have h2 : w * S' < (R + 1) * IPD := by
    have := Nat.lt_mul_div_succ (w * S') hIPD
    rw [← hR] at this
    linarith
  have key : Q2 * φ * IPD ≤ EB * (R + 1) * IPD := by
    calc Q2 * φ * IPD ≤ (EB * (score + bias) / IPD) * φ * IPD :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h0)
      _ = ((EB * (score + bias) / IPD) * IPD) * φ := by ring
      _ ≤ (EB * (score + bias)) * φ := Nat.mul_le_mul_right _ h1
      _ ≤ (EB * S') * w := Nat.mul_le_mul (Nat.mul_le_mul_left _ sc) hw
      _ = EB * (w * S') := by ring
      _ ≤ EB * ((R + 1) * IPD) := Nat.mul_le_mul_left _ h2.le
      _ = EB * (R + 1) * IPD := by ring
  exact Nat.le_of_mul_le_mul_right key hIPD

/-- The floor path falls by the penalty of its epoch. -/
private theorem floor_succ (x : ForkedBeaconState preset) (high t : ℕ) :
    stakeFloorAt config x high (t + 1) = stakeFloorAt config x high t -
      epochPenalty preset config (startInactivityScore config x)
        (stakeCeilingAt config x high t + slashedUnwithdrawnStake x)
        (stakeFloorAt config x high t) t := by
  rfl

/-- The pass rate of a key against the fall of the floor path.

The floor lies below the total active balance read by the pass, and below the weight of the penalty.

The floor after the epoch is positive, so its fall is the penalty.

The score of the key at the pass, plus the bias, is within that of the penalty.

The rate times the floor is at most the key's effective balance times the fall, plus one. -/
private theorem passRate_mul_le {x z : ForkedBeaconState preset} (high t i : ℕ)
    (total : Gwei) (totalOk : getTotalActiveBalance z.state = .ok total)
    (floor : stakeFloorAt config x high t ≤ total.toNat)
    (floorLe : stakeFloorAt config x high t ≤
      stakeCeilingAt config x high t + slashedUnwithdrawnStake x)
    (positive : 0 < stakeFloorAt config x high (t + 1))
    (divisor : 0 < inactivityPenaltyDivisor preset config)
    (factor : 1 ≤ preset.BASE_REWARD_FACTOR.toNat)
    (scored : (if altair : .altair ≤ z.fork then
        (((z.state.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 else 0) +
      config.INACTIVITY_SCORE_BIAS.toNat ≤
        startInactivityScore config x + config.INACTIVITY_SCORE_BIAS.toNat * (t + 1)) :
    PinDrift.Internal.passPenaltyRate config z i * stakeFloorAt config x high t ≤
      effectiveAt z i *
        (stakeFloorAt config x high t - stakeFloorAt config x high (t + 1) + 1) := by
  have succ := floor_succ (config := config) x high t
  have pen : stakeFloorAt config x high t - stakeFloorAt config x high (t + 1) =
      epochPenalty preset config (startInactivityScore config x)
        (stakeCeilingAt config x high t + slashedUnwithdrawnStake x)
        (stakeFloorAt config x high t) t := by omega
  rw [pen]
  have fpos : 0 < stakeFloorAt config x high t := by omega
  have rootPos : 0 < (stakeFloorAt config x high t).sqrt := Nat.sqrt_pos.mpr fpos
  have roots := Nat.sqrt_le_sqrt floor
  have quotient : inactivityPenaltyDivisor preset config ≤ config.INACTIVITY_SCORE_BIAS.toNat *
      (EthLib.Consensus.parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat := by
    unfold inactivityPenaltyDivisor
    apply Nat.mul_le_mul_left
    simp only [EthLib.Consensus.parameters]
    split_ifs <;> omega
  have first := pass_first (TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat)
    WEIGHT_DENOMINATOR.toNat (3 + BASE_REWARDS_PER_EPOCH.toNat) BASE_REWARDS_PER_EPOCH.toNat
    preset.BASE_REWARD_FACTOR.toNat (effectiveAt z i) (stakeFloorAt config x high t)
    (stakeCeilingAt config x high t + slashedUnwithdrawnStake x)
    (stakeFloorAt config x high t).sqrt total.toNat.sqrt (by decide) (by decide) rootPos
    roots (Nat.sqrt_le_self _) floorLe factor (by decide)
  have second := pass_second config.INACTIVITY_SCORE_BIAS.toNat
    (EthLib.Consensus.parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat
    (inactivityPenaltyDivisor preset config) (effectiveAt z i) _
    (startInactivityScore config x + config.INACTIVITY_SCORE_BIAS.toNat * (t + 1))
    (stakeFloorAt config x high t)
    (stakeCeilingAt config x high t + slashedUnwithdrawnStake x) divisor quotient scored floorLe
  unfold PinDrift.Internal.passPenaltyRate epochPenalty
  dsimp only
  rw [← getTotalActiveBalance_toNat totalOk]
  rw [add_mul]
  linarith

end FloorPath

/-! ## One epoch of a new key -/

section Epoch

open DirectSafety.Apriori DirectSafety.Apriori.Internal

/-- One epoch with no pass, and the penalty of a slashing in it. -/
private theorem same_arith (b' b cap K band X sl Q Bq EB : ℕ)
    (hcap : K ≤ cap) (hQ : 2 ≤ Q) (hB : K + band ≤ Q * Bq)
    (seg : min b' cap ≤ b + X + sl) (hsl : Q * sl ≤ EB)
    (hyst : EB ≤ b' + band) (hcapEB : EB ≤ cap) :
    min b' K ≤ b + X + (if sl = 0 then 0 else Bq) := by
  by_cases z : sl = 0
  · subst z
    simp only [ite_true] at *
    have : min b' K ≤ min b' cap := min_le_min_left _ hcap
    omega
  · simp only [z, ite_false]
    obtain ⟨hEB, hcle⟩ := eb_le_min_band b' cap K band EB hcap hyst hcapEB
    set C := min b' cap with hC
    by_cases cK : C ≤ K
    · have slB : sl ≤ Bq := by
        have : Q * sl ≤ Q * Bq := by omega
        exact Nat.le_of_mul_le_mul_left this (by omega)
      omega
    · have above : K < C := Nat.lt_of_not_ge cK
      have : min b' K = K := by
        apply min_eq_right
        have := min_le_left b' cap
        omega
      rw [this]
      have : Q * sl ≤ Q * (Bq + (C - K)) := by
        have h1 : Q * (C - K) ≥ C - K := Nat.le_mul_of_pos_left _ (by omega)
        have : Q * (Bq + (C - K)) = Q * Bq + Q * (C - K) := by ring
        omega
      have := Nat.le_of_mul_le_mul_left this (by omega)
      omega

/-- The charge for the slashing of a key: the rounded-up initial penalty of the least stake. -/
private def newBq (preset : Preset) : ℕ :=
  (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
    (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat - 1) /
      (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat

/-- The standing hypotheses of the floor of a new key.

They are the guard and the facts that it reads.

They also hold the preset facts that the floor reads. -/
private structure Ctx (config : Config) (checks : SignatureChecks) {preset : Preset}
    (g x : ForkedBeaconState preset) (high : ℕ) where
  shared : Run config checks g x
  genesis : Genesis (config := config) (checks := checks) g
  parameters : DirectSafety.Parameters preset
  caps : CapOrder preset
  aligned : MaxEffectiveBalancesAligned preset
  twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat
  electra : .pectra ≤ x.fork
  fulu : .fusaka ≤ x.fork
  guard : aprioriGuardAt config x high
  delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  vector : 4 ≤ preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat
  big : 9 * (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat ≤
    stakeFloorAt config x high 0
  factor : 1 ≤ preset.BASE_REWARD_FACTOR.toNat
  quotientTwo :
    2 ≤ (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat
  margin : 2400 * (2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
      preset.MAX_EFFECTIVE_BALANCE.toNat /
        (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
      preset.downwardBand - 1) + 2400 * preset.downwardBand + 2400 * newBq preset ≤
    1591 * (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand)
  room : 600 * (high + 2 - (getCurrentEpoch x.state).toNat) ≤ stakeFloorAt config x high 0
  bands : preset.IncrementWithinUpwardBand

/-- Along the window, the floor stays within three halves of its start.

The start floor is below the stake at the start, which the funded stake covers.

The funded stake is below the first ceiling, which is below the last.

The guard asks that twice the last ceiling be at most three times the last floor. -/
private theorem Ctx.ratio {g x : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (early : x.fork < .glamsterdam) {s : ℕ}
    (inside : s ≤ high + 1 - (getCurrentEpoch x.state).toNat) :
    2 * stakeFloorAt config x high 0 ≤ 3 * stakeFloorAt config x high s := by
  have ratio := PinDrift.Internal.ratio_of_guard c.electra c.guard
  have first : stakeFloorAt config x high 0 ≤ stakeCeilingAt config x high 0 :=
    (floor_initial_le_reference x high).trans
      ((funding_active_le x early (c.shared.pubkeysDistinct c.genesis)).trans
        (funded_le_ceiling_initial c.electra))
  have anti : stakeFloorAt config x high (high + 1 - (getCurrentEpoch x.state).toNat) ≤
      stakeFloorAt config x high s := PinDrift.Internal.stakeFloorAt_anti inside
  have mono : stakeCeilingAt config x high 0 ≤
      stakeCeilingAt config x high (high + 1 - (getCurrentEpoch x.state).toNat) :=
    PinDrift.Internal.stakeCeilingAt_mono c.electra (Nat.zero_le _)
  omega

/-- The debits of key `i` in a list of events: its sync debits and its partial payments. -/
private def keyDebits (i : ℕ) (events : List (BalanceEvent preset)) : ℕ :=
  (events.map (PinDrift.Internal.syncDebit i)).sum + (events.map (floorPartialDebit i.toUInt64)).sum

/-- The debits of a key add up over two lists of events. -/
private theorem keyDebits_append (i : ℕ) (a b : List (BalanceEvent preset)) :
    keyDebits i (a ++ b) = keyDebits i a + keyDebits i b := by
  simp only [keyDebits, List.map_append, List.sum_append]
  omega

/-- The key is charged `newBq` once it is slashed. -/
private def slashedCharge (preset : Preset) (s : ForkedBeaconState preset) (i : ℕ) : ℕ :=
  if ∃ w, s.state.validators.data[i]? = some w ∧ w.slashed = true then newBq preset else 0

/-- The potential claim at an epoch start `m`, along a run `rm` from the start `z` of the climb.

The potential of the key keeps the fraction of the floor that the floor keeps since `z`.

The potential counts the debits of the key and its slashing charge along `rm`. -/
private def EpochClaim (x z : ForkedBeaconState preset) (high i : ℕ) {m : ForkedBeaconState preset}
    (rm : Run config checks z m) : Prop :=
  ∃ events, rm.balanceEvents high = .ok events ∧
    2 * (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) *
        stakeFloorAt config x high
          ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) ≤
      2 * (min (actualBalanceAt m i) preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
          keyDebits i events + slashedCharge preset m i) *
        stakeFloorAt config x high
          ((getCurrentEpoch z.state).toNat - (getCurrentEpoch x.state).toNat) +
      3 * (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) *
        ((getCurrentEpoch m.state).toNat - (getCurrentEpoch z.state).toNat)

/-- The facts on the cap and the slashing charge that each step of the floor of a key reads.

The slashing quotient is positive.

The cap lies above `MAX_EFFECTIVE_BALANCE` and above the key's effective balance.

The charge `newBq` covers `MAX_EFFECTIVE_BALANCE` and the band in units of the quotient. -/
private theorem Ctx.step_facts {g x m : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hm : Run config checks x m) (mEarly : m.fork < .glamsterdam)
    {i : ℕ} {val : Validator} (found : m.state.validators.data[i]? = some val) :
    0 < (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
      preset.MAX_EFFECTIVE_BALANCE.toNat ≤
        (withdrawalMaxEffectiveBalance preset m.fork val).toNat ∧
      effectiveAt m i ≤ (withdrawalMaxEffectiveBalance preset m.fork val).toNat ∧
      preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand ≤
        (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat *
          ((preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
            (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat - 1) /
            (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat) := by
  have positiveQ :
      0 < (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat := by
    have := c.quotientTwo
    omega
  refine ⟨positiveQ,
    UInt64.le_iff_toNat_le.mp (Internal.minimum_cap c.caps.activation c.caps.compounding val),
    ?_, le_smul_ceilDiv (β := Nat) positiveQ⟩
  have := Run.effectiveBalance_capped (c.shared.append hm) c.genesis c.caps.activation
    c.caps.compounding mEarly val (Array.mem_of_getElem? found)
  have e : effectiveAt m i = val.effectiveBalance.toNat := by simp [effectiveAt, found]
  rw [e]
  exact UInt64.le_iff_toNat_le.mp this

/-- A step is charged `Bq` for a slashing only when the key is slashed in it. -/
private theorem charge_le (P : Prop) [Decidable P] (a Q Bq : ℕ) :
    (if (if P then a / Q else 0) = 0 then 0 else Bq) ≤ (if P then Bq else 0) := by
  by_cases h : P <;> by_cases e : a / Q = 0 <;> simp [h, e]

/-- The floor of a new key over one epoch that a slot step ends.

The potential of a key is the least of its balance and `MAX_EFFECTIVE_BALANCE`, plus the band.

The potential at the start keeps the fraction of the floor, less the rounding error.

It is charged the key's sync debits, its partial payments, and its slashing, once. -/
private theorem Ctx.cross {g x m n z : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hm : Run config checks x m)
    (pre : Run config checks m z) (ok : advanceSlotAcross config checks z = .ok n)
    (early : n.fork < .glamsterdam)
    (within : (getCurrentEpoch n.state).toNat ≤ high + 1)
    (same : getCurrentEpoch z.state = getCurrentEpoch m.state)
    (step : (getCurrentEpoch n.state).toNat = (getCurrentEpoch m.state).toNat + 1)
    (i : ℕ) (val : Validator) (found : m.state.validators.data[i]? = some val)
    (activated : val.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (exit : ∀ w, n.state.validators.data[i]? = some w →
      (getCurrentEpoch m.state).toNat + 1 < w.exitEpoch.toNat)
    (slashedCond : val.slashed = true → (getCurrentEpoch n.state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 < val.withdrawableEpoch.toNat)
    (hyst : effectiveAt m i ≤ actualBalanceAt m i + preset.downwardBand)
    {events : List (BalanceEvent preset)}
    (replayed : (pre.snoc (Step.slot ok)).balanceEvents (getCurrentEpoch m.state).toNat =
      .ok events) :
    (min (actualBalanceAt m i) preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) *
        stakeFloorAt config x high
          ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1) ≤
      (min (actualBalanceAt n i) preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) *
          stakeFloorAt config x high
            ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) +
        (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) +
        ((events.map (PinDrift.Internal.syncDebit i)).sum + (events.map (floorPartialDebit
          i.toUInt64)).sum +
          (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
            then (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
              (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
                1) /
              (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat
            else 0)) *
          stakeFloorAt config x high
            ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) := by
  classical
  have mz := fork_le_of_chainSteps pre.chainSteps
  have hxm := fork_le_of_chainSteps hm.chainSteps
  have zn : z.fork ≤ n.fork := (Step.slot ok).chainStep.fork_le
  have mEarly : m.fork < .glamsterdam := Nat.lt_of_le_of_lt (Nat.le_trans mz zn) early
  have fuluM : .fusaka ≤ m.fork := Nat.le_trans c.fulu hxm
  have shared' := c.shared.append hm
  have xm := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps hm.chainSteps)
  obtain ⟨positiveQ, capLe, capEB, hB⟩ := c.step_facts hm mEarly found
  obtain ⟨z', pre', post', hr, hz', ineq⟩ := epochFloor shared' c.genesis c.caps c.delay
    c.vector positiveQ (pre.snoc (Step.slot ok)) fuluM early
    (Or.inr ⟨z, pre, ok, rfl, same, step⟩) i val found activated exit slashedCond
    (withdrawalMaxEffectiveBalance preset m.fork val).toNat le_rfl replayed
  have zForkLe : z'.fork ≤ n.fork := fork_le_of_chainSteps post'.chainSteps
  have z'Early : z'.fork < .glamsterdam := Nat.lt_of_le_of_lt zForkLe early
  have z'x : Run config checks x z' := hm.append pre'
  have z'epoch : (getCurrentEpoch z'.state).toNat = (getCurrentEpoch m.state).toNat :=
    congrArg UInt64.toNat hz'
  have nz' := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post'.chainSteps)
  have insideM : i < m.state.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
  have effEq : effectiveAt z' i = effectiveAt m i :=
    run_same_epoch_effective pre' z'Early hz' i insideM
  have altairX : .altair ≤ x.fork := Nat.le_trans (by decide) c.fulu
  have altairZ : .altair ≤ z'.fork :=
    Nat.le_trans altairX (Nat.le_trans hxm (fork_le_of_chainSteps pre'.chainSteps))
  have pass : (if getCurrentEpoch m.state < getCurrentEpoch n.state ∧
        ∃ total, getTotalActiveBalance z'.state = .ok total then
          PinDrift.Internal.passPenaltyRate config z' i else 0) *
      stakeFloorAt config x high
        ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) ≤
      effectiveAt m i * (stakeFloorAt config x high
        ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) -
          stakeFloorAt config x high
            ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1) + 1) := by
    by_cases h : ∃ total, getTotalActiveBalance z'.state = .ok total
    · obtain ⟨total, totalOk⟩ := h
      have lt : getCurrentEpoch m.state < getCurrentEpoch n.state :=
        UInt64.lt_iff_toNat_lt.mpr (by omega)
      rw [ite_eq_left ⟨lt, total, totalOk⟩]
      have bounds := PinDrift.Internal.total_within_guard c.shared c.genesis c.parameters c.caps
        c.aligned c.twoSlots
        c.electra c.guard z'x z'Early (by omega) totalOk
      have ixeq : ix x z' = (getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat := by
        simp only [ix]
        omega
      rw [ixeq] at bounds
      have positive : 0 < stakeFloorAt config x high
          ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1) :=
        c.guard.2.2.2.2.2.2.2.2.2.2.2.1 _ (by unfold driftHorizon; omega)
      have divisor : 0 < inactivityPenaltyDivisor preset config := c.guard.2.2.2.2.2.2.1
      have scored : (if altair : .altair ≤ z'.fork then
          (((z'.state.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 else 0) +
            config.INACTIVITY_SCORE_BIAS.toNat ≤ startInactivityScore config x +
          config.INACTIVITY_SCORE_BIAS.toNat * ((getCurrentEpoch m.state).toNat -
            (getCurrentEpoch x.state).toNat + 1) := by
        rw [dite_eq_left altairZ]
        have grow : config.INACTIVITY_SCORE_BIAS.toNat ≤ config.INACTIVITY_SCORE_BIAS.toNat *
            ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1) :=
          Nat.le_mul_of_pos_right _ (by omega)
        cases found' : (z'.state.inactivityScores altairZ).data[i]? with
        | none =>
          simp only [Option.map_none, Option.getD_none]
          omega
        | some score =>
          have := runScores_le z'x altairX z'Early (Or.inl c.electra) altairZ found'
          simp only [Option.map_some, Option.getD_some]
          have e : (getCurrentEpoch z'.state).toNat - (getCurrentEpoch x.state).toNat =
              (getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat := by omega
          rw [e] at this
          rw [Nat.mul_add, Nat.mul_one]
          omega
      have := passRate_mul_le (config := config) (x := x) (z := z') high
        ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) i total totalOk
        bounds.1 (by omega) positive divisor c.factor scored
      rw [effEq] at this
      exact this
    · rw [ite_eq_right (fun h' => h h'.2)]
      simp
  rw [mspq_fusaka fuluM] at ineq
  set K := preset.MAX_EFFECTIVE_BALANCE.toNat with hK
  set Q := (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat
    with hQ
  set band := preset.downwardBand with hband
  set t := (getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat with ht
  set Bq := (K + band + Q - 1) / Q with hBq
  have hanti : stakeFloorAt config x high (t + 1) ≤ stakeFloorAt config x high t :=
    PinDrift.Internal.stakeFloorAt_anti (Nat.le_succ t)
  have hzero : stakeFloorAt config x high t ≤ stakeFloorAt config x high 0 :=
    PinDrift.Internal.stakeFloorAt_anti (Nat.zero_le t)
  have nWithin := step
  have cxIn : (getCurrentEpoch x.state).toNat ≤ high + 1 := by omega
  have xEarly : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Nat.le_trans hxm (Nat.le_trans mz zn)) early
  have ratio := c.ratio xEarly (s := t + 1) (by omega)
  have roomT := c.room
  have hφ : 6 * Q ≤ stakeFloorAt config x high (t + 1) := by
    have := c.big
    omega
  have hband' : 2 * stakeFloorAt config x high t ≤ 3 * stakeFloorAt config x high (t + 1) := by
    omega
  have bound := step_arith_slash (actualBalanceAt m i) (actualBalanceAt n i)
    (withdrawalMaxEffectiveBalance preset m.fork val).toNat K band
    (if getCurrentEpoch m.state < getCurrentEpoch n.state ∧
        ∃ total, getTotalActiveBalance z'.state = .ok total then PinDrift.Internal.passPenaltyRate
          config z' i else 0)
    ((events.map (PinDrift.Internal.syncDebit i)).sum + (events.map (floorPartialDebit
      i.toUInt64)).sum)
    (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
      then effectiveAt m i / Q else 0)
    Q Bq (stakeFloorAt config x high t) (stakeFloorAt config x high (t + 1))
    (stakeFloorAt config x high t - stakeFloorAt config x high (t + 1)) (effectiveAt m i)
    capLe c.quotientTwo hB (by omega)
    (by split <;> [exact Nat.mul_div_le _ _; simp])
    hyst capEB pass (by omega) hφ hband'
  have charge := charge_le
    (val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true)
    (effectiveAt m i) Q Bq
  have mul := Nat.mul_le_mul_right (stakeFloorAt config x high t)
    (Nat.add_le_add_left charge ((events.map (PinDrift.Internal.syncDebit i)).sum +
      (events.map (floorPartialDebit i.toUInt64)).sum))
  linarith

/-- The floor of a new key over a run inside one epoch.

The least of its balance and `MAX_EFFECTIVE_BALANCE` at the start is at most its balance at the end.

It is charged the key's sync debits, its partial payments, and its slashing, once. -/
private theorem Ctx.inside {g x m n : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hm : Run config checks x m) (seg : Run config checks m n)
    (early : n.fork < .glamsterdam)
    (same : getCurrentEpoch n.state = getCurrentEpoch m.state)
    (i : ℕ) (val : Validator) (found : m.state.validators.data[i]? = some val)
    (activated : val.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (exit : ∀ w, n.state.validators.data[i]? = some w →
      (getCurrentEpoch m.state).toNat + 1 < w.exitEpoch.toNat)
    (slashedCond : val.slashed = true → (getCurrentEpoch n.state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 < val.withdrawableEpoch.toNat)
    (hyst : effectiveAt m i ≤ actualBalanceAt m i + preset.downwardBand)
    {events : List (BalanceEvent preset)}
    (replayed : seg.balanceEvents (getCurrentEpoch m.state).toNat = .ok events) :
    min (actualBalanceAt m i) preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt n i +
      ((events.map (PinDrift.Internal.syncDebit i)).sum + (events.map (floorPartialDebit
        i.toUInt64)).sum +
        (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
          then (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
            (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
              1) / (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat
          else 0)) := by
  classical
  have hxm := fork_le_of_chainSteps hm.chainSteps
  have mn := fork_le_of_chainSteps seg.chainSteps
  have mEarly : m.fork < .glamsterdam := Nat.lt_of_le_of_lt mn early
  have fuluM : .fusaka ≤ m.fork := Nat.le_trans c.fulu hxm
  have shared' := c.shared.append hm
  obtain ⟨positiveQ, capLe, capEB, hB⟩ := c.step_facts hm mEarly found
  obtain ⟨z', pre', post', hr, hz', ineq⟩ := epochFloor shared' c.genesis c.caps c.delay
    c.vector positiveQ seg fuluM early (Or.inl same) i val found activated exit slashedCond
    (withdrawalMaxEffectiveBalance preset m.fork val).toNat le_rfl replayed
  rw [mspq_fusaka fuluM] at ineq
  have noPass : ¬ (getCurrentEpoch m.state < getCurrentEpoch n.state ∧
      ∃ total, getTotalActiveBalance z'.state = .ok total) := by
    intro h
    rw [same] at h
    exact UInt64.lt_irrefl _ h.1
  rw [ite_eq_right noPass] at ineq
  set K := preset.MAX_EFFECTIVE_BALANCE.toNat with hK
  set Q := (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat
    with hQ
  set band := preset.downwardBand with hband
  set Bq := (K + band + Q - 1) / Q with hBq
  have bound := same_arith (actualBalanceAt m i) (actualBalanceAt n i)
    (withdrawalMaxEffectiveBalance preset m.fork val).toNat K band
    ((events.map (PinDrift.Internal.syncDebit i)).sum + (events.map (floorPartialDebit
      i.toUInt64)).sum)
    (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
      then effectiveAt m i / Q else 0)
    Q Bq (effectiveAt m i) capLe c.quotientTwo hB (by omega)
    (by split <;> [exact Nat.mul_div_le _ _; simp]) hyst capEB
  have charge := charge_le
    (val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true)
    (effectiveAt m i) Q Bq
  omega

/-- Right after an epoch transition, the effective balance of a key is within the band.

The band lies above its balance. -/
private theorem Ctx.hyst_start {g x m : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hm : Run config checks x m)
    (hyst : Hysteresis m.state) {i : ℕ} {val : Validator}
    (found : m.state.validators.data[i]? = some val) :
    effectiveAt m i ≤ actualBalanceAt m i + preset.downwardBand := by
  have matched := (run_justified_separated (c.shared.append hm) c.genesis).1.balancesMatch
  have lt : i < m.state.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
  have lt' : i < m.state.balances.data.size := by
    unfold BalancesMatch at matched
    omega
  have bal : m.state.balances.data[i]? = some m.state.balances.data[i] :=
    Array.getElem?_eq_getElem lt'
  have := hyst.down i val _ found bal
  simp only [effectiveAt, actualBalanceAt, found, bal, Option.map_some, Option.getD_some]
  exact this

/-- The arithmetic of the last step of the floor of a new key.

The potential keeps `2/3` of its start, less the rounding, and the rounding is below the room.

The preset fact `margin` then leaves the floor of the pin. -/
private theorem final_arith (K band Bq B S C φ0 φk J J' T : ℕ)
    (h1 : 2 * (K + band) * φk ≤ 2 * (B + band + C) * φ0 + 3 * (K + band) * J)
    (h2 : 2 * φ0 ≤ 3 * φk) (hJ : J ≤ J') (room : 400 * J' ≤ φ0) (pos : 0 < φ0)
    (hC : C ≤ S + Bq)
    (margin : 2400 * T + 2400 * band + 2400 * Bq ≤ 1591 * (K + band)) : T ≤ B + S := by
  have a1 : 6 * (K + band) * φk ≤ 6 * (B + band + C) * φ0 + 9 * (K + band) * J := by nlinarith
  have a2 : 4 * (K + band) * φ0 ≤ 6 * (K + band) * φk := by nlinarith
  have a3 : 9 * (K + band) * J * 400 ≤ 9 * (K + band) * φ0 := by
    have : J * 400 ≤ φ0 := by omega
    nlinarith
  have a4 : 1600 * (K + band) * φ0 ≤ 2400 * (B + band + C) * φ0 + 9 * (K + band) * φ0 := by
    nlinarith
  have a5 : 1600 * (K + band) ≤ 2400 * (B + band + C) + 9 * (K + band) := by
    have := Nat.le_of_mul_le_mul_right (a := 1600 * (K + band))
      (b := 2400 * (B + band + C) + 9 * (K + band)) (c := φ0) (by nlinarith) pos
    exact this
  omega

/-- A key slashed on the climb is not due its delayed penalty within the window.

It was unslashed at the start `z` of the climb, so its withdrawal waits a whole slashings vector. -/
private theorem Ctx.slashed_window {g x z m : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hz : Run config checks x z) (rm : Run config checks z m)
    (mEarly : m.fork < .glamsterdam) (i : ℕ) (v0 val : Validator)
    (found0 : z.state.validators.data[i]? = some v0)
    (found : m.state.validators.data[i]? = some val)
    (unslashed0 : v0.slashed = false) (epoch : ℕ) (inside : epoch ≤ high + 1) :
    val.slashed = true →
      epoch + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 < val.withdrawableEpoch.toNat := by
  intro flag
  have lower := rm.newly_slashed_withdrawableEpoch c.caps.activation c.caps.compounding
    mEarly c.delay i v0 val found0 found unslashed0 flag
  have window := c.guard.2.2.2.2.2.2.2.2.2.2.1
  have xz := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps hz.chainSteps)
  unfold driftHorizon at window
  omega

/-- The slashing charge of a run adds the charge of its slashing. -/
private theorem slashedCharge_run {m n : ForkedBeaconState preset} (seg : Run config checks m n)
    (i : ℕ) (val : Validator) (found : m.state.validators.data[i]? = some val) :
    slashedCharge preset n i = slashedCharge preset m i +
      (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
        then newBq preset else 0) := by
  classical
  unfold slashedCharge
  by_cases flag : val.slashed = true
  · obtain ⟨w', wFound', wFlag⟩ := seg.slashedPersistence i val found flag
    have : ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true := ⟨w', wFound', wFlag⟩
    have fm : ∃ w, m.state.validators.data[i]? = some w ∧ w.slashed = true := ⟨val, found, flag⟩
    simp [this, fm, flag]
  · have flag' : val.slashed = false := by simpa using flag
    have fm : ¬ ∃ w, m.state.validators.data[i]? = some w ∧ w.slashed = true := by
      rintro ⟨w', h, hf⟩
      rw [found] at h
      cases h
      exact flag hf
    simp [fm, flag']

/-- The potential claim passes the slot step that ends an epoch.

The step is the cross of one epoch, so the claim holds for the next epoch start, one epoch on. -/
private theorem Ctx.advance {g x z m p n : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hz : Run config checks x z) (rm : Run config checks z m)
    (ins : Run config checks m p) (ok : advanceSlotAcross config checks p = .ok n)
    (early : n.fork < .glamsterdam) (within : (getCurrentEpoch n.state).toNat ≤ high + 1)
    (same : getCurrentEpoch p.state = getCurrentEpoch m.state)
    (step : (getCurrentEpoch n.state).toNat = (getCurrentEpoch m.state).toNat + 1)
    (i : ℕ) (val : Validator) (found : m.state.validators.data[i]? = some val)
    (activated : val.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (exit : ∀ w, n.state.validators.data[i]? = some w →
      (getCurrentEpoch m.state).toNat + 1 < w.exitEpoch.toNat)
    (slashedCond : val.slashed = true → (getCurrentEpoch n.state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 < val.withdrawableEpoch.toNat)
    (hyst : effectiveAt m i ≤ actualBalanceAt m i + preset.downwardBand)
    (claim : EpochClaim (config := config) (checks := checks) x z high i rm) :
    EpochClaim (config := config) (checks := checks) x z high i
      (rm.append (ins.snoc (Step.slot ok))) := by
  classical
  obtain ⟨events, replay, ih⟩ := claim
  have mp := fork_le_of_chainSteps ins.chainSteps
  have pn : p.fork ≤ n.fork := (Step.slot ok).chainStep.fork_le
  have hm : Run config checks x m := hz.append rm
  have mEarly : m.fork < .glamsterdam := Nat.lt_of_le_of_lt (Nat.le_trans mp pn) early
  have xm := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps hm.chainSteps)
  have zm := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rm.chainSteps)
  have xz := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps hz.chainSteps)
  -- the events of the segment
  obtain ⟨eseg, hseg⟩ := (ins.snoc (Step.slot ok)).balanceEvents_ok early high
  have local_ : (ins.snoc (Step.slot ok)).balanceEvents (getCurrentEpoch m.state).toNat =
      .ok eseg := by
    rw [← balanceEvents_eq_of_endpoint_le (ins.snoc (Step.slot ok)) within (by omega)]
    exact hseg
  have whole := balanceEvents_append rm (ins.snoc (Step.slot ok)) high replay hseg
  have crossed := Ctx.cross c hm ins ok early within same step i val found activated exit
    slashedCond hyst local_
  have charge := slashedCharge_run (ins.snoc (Step.slot ok)) i val found
  have xEarly : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Nat.le_trans (fork_le_of_chainSteps hm.chainSteps) (Nat.le_trans mp pn))
      early
  have cxIn : (getCurrentEpoch x.state).toNat ≤ high + 1 := by omega
  have pos : 0 < stakeFloorAt config x high
      ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) :=
    c.guard.2.2.2.2.2.2.2.2.2.2.2.1 _ (by unfold driftHorizon; omega)
  have hanti : stakeFloorAt config x high
      ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1) ≤
        stakeFloorAt config x high
          ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) :=
    PinDrift.Internal.stakeFloorAt_anti (Nat.le_succ _)
  have hzero : stakeFloorAt config x high
      ((getCurrentEpoch z.state).toNat - (getCurrentEpoch x.state).toNat) ≤
        stakeFloorAt config x high 0 := PinDrift.Internal.stakeFloorAt_anti (Nat.zero_le _)
  have ratio := c.ratio xEarly (s := (getCurrentEpoch m.state).toNat -
    (getCurrentEpoch x.state).toNat) (by omega)
  have band : 2 * stakeFloorAt config x high
      ((getCurrentEpoch z.state).toNat - (getCurrentEpoch x.state).toNat) ≤
      3 * stakeFloorAt config x high
        ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) := by omega
  have e1 : (getCurrentEpoch n.state).toNat - (getCurrentEpoch x.state).toNat =
      (getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1 := by omega
  refine ⟨events ++ eseg, whole, ?_⟩
  rw [e1, charge, keyDebits_append]
  have crossed' : (min (actualBalanceAt m i) preset.MAX_EFFECTIVE_BALANCE.toNat +
        preset.downwardBand) *
      stakeFloorAt config x high
        ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1) ≤
      (min (actualBalanceAt n i) preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) *
          stakeFloorAt config x high
            ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) +
        (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) +
        (keyDebits i eseg + (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧
            w.slashed = true then newBq preset else 0)) *
          stakeFloorAt config x high
            ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) := crossed
  have mono : (keyDebits i events + slashedCharge preset m i) *
      stakeFloorAt config x high
        ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1) ≤
      (keyDebits i events + slashedCharge preset m i) *
        stakeFloorAt config x high
          ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) :=
    Nat.mul_le_mul_left _ hanti
  have stepIneq := chain_step (stakeFloorAt config x high
      ((getCurrentEpoch z.state).toNat - (getCurrentEpoch x.state).toNat))
    (stakeFloorAt config x high
      ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat))
    (stakeFloorAt config x high
      ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1))
    (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand)
    (min (actualBalanceAt m i) preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
      keyDebits i events + slashedCharge preset m i)
    (min (actualBalanceAt n i) preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
      (keyDebits i events + keyDebits i eseg) +
      (slashedCharge preset m i + (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? =
        some w ∧ w.slashed = true then newBq preset else 0)))
    (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand)
    ((getCurrentEpoch m.state).toNat - (getCurrentEpoch z.state).toNat) pos hanti band ih
    (by nlinarith [crossed', mono])
  have e2 : (getCurrentEpoch n.state).toNat - (getCurrentEpoch z.state).toNat =
      (getCurrentEpoch m.state).toNat - (getCurrentEpoch z.state).toNat + 1 := by omega
  rw [e2]
  exact stepIneq

/-- The potential claim carries over the slot step that ends the epoch of a climb state.

The new epoch start also lies within the band of hysteresis, since the step ran the transition. -/
private theorem Ctx.inv_step {g x z y q p' m : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hz : Run config checks x z)
    (early : y.fork < .glamsterdam) (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (i : ℕ) (v0 : Validator) (found0 : z.state.validators.data[i]? = some v0)
    (unslashed0 : v0.slashed = false) (activated0 : v0.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (exitLate : ∀ (n : ForkedBeaconState preset) (_rest : Run config checks n y) (w : Validator),
      n.state.validators.data[i]? = some w → (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat)
    (ok : advanceSlotAcross config checks q = .ok p') (rest : Run config checks p' y)
    (rm : Run config checks z m) (ins : Run config checks m q)
    (cm : getCurrentEpoch m.state = getCurrentEpoch q.state)
    (hyst : effectiveAt m i ≤ actualBalanceAt m i + preset.downwardBand)
    (claim : EpochClaim (config := config) (checks := checks) x z high i rm)
    (stepQ : (getCurrentEpoch p'.state).toNat = (getCurrentEpoch q.state).toNat + 1) :
    EpochClaim (config := config) (checks := checks) x z high i
      (rm.append (ins.snoc (Step.slot ok))) ∧
    effectiveAt p' i ≤ actualBalanceAt p' i + preset.downwardBand := by
  have restEpoch := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest.chainSteps)
  have pEarly : p'.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) early
  have cmN : (getCurrentEpoch m.state).toNat = (getCurrentEpoch q.state).toNat :=
    congrArg UInt64.toNat cm
  obtain ⟨val, found, life⟩ := rm.registryLifecycle.validators i v0 found0
  have activated : val.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    rw [life.activationEpoch activated0]
    exact activated0
  have mEarly : m.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Nat.le_trans (fork_le_of_chainSteps ins.chainSteps)
      (Step.slot ok).chainStep.fork_le) pEarly
  have slashedCond := c.slashed_window hz rm mEarly i v0 val found0 found unslashed0
    (getCurrentEpoch p'.state).toNat (by omega)
  have sameQ : getCurrentEpoch q.state = getCurrentEpoch m.state := cm.symm
  have stepP : (getCurrentEpoch p'.state).toNat = (getCurrentEpoch m.state).toNat + 1 := by
    omega
  have exit' : ∀ w, p'.state.validators.data[i]? = some w →
      (getCurrentEpoch m.state).toNat + 1 < w.exitEpoch.toNat := fun w hw => by
    have := exitLate p' rest w hw
    omega
  have claim' := Ctx.advance c hz rm ins ok pEarly (by omega) sameQ stepP i val found
    activated exit' slashedCond hyst claim
  obtain ⟨val', found', -⟩ := (rm.append (ins.snoc (Step.slot ok))).registryLifecycle.validators
    i v0 found0
  have lt : getCurrentEpoch q.state < getCurrentEpoch p'.state :=
    UInt64.lt_iff_toNat_lt.mpr (by omega)
  have fuluQ : .fusaka ≤ q.fork :=
    Nat.le_trans c.fulu (fork_le_of_chainSteps (hz.append (rm.append ins)).chainSteps)
  exact ⟨claim', Ctx.hyst_start c (hz.append (rm.append (ins.snoc (Step.slot ok))))
    (DirectSafety.Apriori.Internal.hysteresis_of_crossing_slot ok c.bands fuluQ pEarly
      (UInt64.lt_iff_toNat_lt.mp lt)) found'⟩

/-- The potential claim holds at the start of the epoch of every state of the climb.

The climb runs from `z`, where the key holds the maximum effective balance and is unslashed.

The key never exits before the end `y` of the climb.

The state `p` reaches `y`, so it ends no later than `y`. -/
private theorem Ctx.inv {g x z y : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hz : Run config checks x z)
    (early : y.fork < .glamsterdam) (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (i : ℕ) (v0 : Validator) (found0 : z.state.validators.data[i]? = some v0)
    (unslashed0 : v0.slashed = false) (activated0 : v0.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (bal0 : preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt z i)
    (hystZ : effectiveAt z i ≤ actualBalanceAt z i + preset.downwardBand)
    (exitLate : ∀ (n : ForkedBeaconState preset) (_rest : Run config checks n y) (w : Validator),
      n.state.validators.data[i]? = some w → (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat)
    {p : ForkedBeaconState preset} (rp : Run config checks z p) :
    ∀ (_rest : Run config checks p y), ∃ (m : ForkedBeaconState preset)
      (rm : Run config checks z m) (ins : Run config checks m p),
      rp = rm.append ins ∧ getCurrentEpoch m.state = getCurrentEpoch p.state ∧
      effectiveAt m i ≤ actualBalanceAt m i + preset.downwardBand ∧
      EpochClaim (config := config) (checks := checks) x z high i rm := by
  induction rp with
  | nil =>
    intro _
    refine ⟨z, .nil, .nil, rfl, rfl, hystZ, [], rfl, ?_⟩
    have unflagged : ¬ ∃ w, z.state.validators.data[i]? = some w ∧ w.slashed = true := by
      rintro ⟨w, h, hf⟩
      rw [found0] at h
      cases h
      rw [unslashed0] at hf
      cases hf
    have charge : slashedCharge preset z i = 0 := by simp [slashedCharge, unflagged]
    rw [charge, min_eq_right bal0]
    simp [keyDebits]
  | @snoc q p' pre step ih =>
    intro rest
    obtain ⟨m, rm, ins, eq, cm, hyst, claim⟩ := ih ((Run.nil.snoc step).append rest)
    by_cases same : getCurrentEpoch p'.state = getCurrentEpoch q.state
    · refine ⟨m, rm, ins.snoc step, ?_, cm.trans same.symm, hyst, claim⟩
      rw [eq]
      rfl
    · have bound := ChainStep.epoch_le_succ step.chainStep
      have order := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
      have differ : (getCurrentEpoch p'.state).toNat ≠ (getCurrentEpoch q.state).toNat :=
        fun h => same (UInt64.toNat_inj.mp h)
      cases step with
      | @block fork before after engine signed due ok =>
        exfalso
        apply same
        simp only [getCurrentEpoch, processBlock_slot (applySignedBlock_ok ok).2.1]
      | slot ok =>
        obtain ⟨claim', hystP⟩ := Ctx.inv_step c hz early within i v0 found0 unslashed0 activated0
          exitLate ok rest rm ins cm hyst claim (by omega)
        refine ⟨p', rm.append (ins.snoc (Step.slot ok)), .nil, ?_, rfl, hystP, claim'⟩
        rw [eq]
        rfl

/-- The arithmetic of the climb: the potential claim gives the floor of the pin.

The claim starts at the epoch `cz` and ends at the epoch `ck`, within the window. -/
private theorem Ctx.arith {g x : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (xEarly : x.fork < .glamsterdam) (cz ck : ℕ)
    (xz : (getCurrentEpoch x.state).toNat ≤ cz) (zk : cz ≤ ck) (inside : ck ≤ high + 1)
    (B kd sc : ℕ) (hsc : sc ≤ newBq preset)
    (claim : 2 * (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) *
        stakeFloorAt config x high (ck - (getCurrentEpoch x.state).toNat) ≤
      2 * (B + preset.downwardBand + (kd + sc)) *
        stakeFloorAt config x high (cz - (getCurrentEpoch x.state).toNat) +
      3 * (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) * (ck - cz)) :
    2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
        preset.MAX_EFFECTIVE_BALANCE.toNat /
          (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        preset.downwardBand - 1 ≤ B + kd := by
  have cxIn : (getCurrentEpoch x.state).toNat ≤ high + 1 := by omega
  have ratio0 := c.ratio xEarly (s := cz - (getCurrentEpoch x.state).toNat) (by omega)
  have ratioK := c.ratio xEarly (s := ck - (getCurrentEpoch x.state).toNat) (by omega)
  have hzero : stakeFloorAt config x high (cz - (getCurrentEpoch x.state).toNat) ≤
      stakeFloorAt config x high 0 := PinDrift.Internal.stakeFloorAt_anti (Nat.zero_le _)
  have roomT := c.room
  have unitJ : 1 ≤ high + 2 - (getCurrentEpoch x.state).toNat := by omega
  have phi : 2 * stakeFloorAt config x high (cz - (getCurrentEpoch x.state).toNat) ≤
      3 * stakeFloorAt config x high (ck - (getCurrentEpoch x.state).toNat) := by omega
  exact final_arith preset.MAX_EFFECTIVE_BALANCE.toNat preset.downwardBand (newBq preset) B kd
    (kd + sc) (stakeFloorAt config x high (cz - (getCurrentEpoch x.state).toNat))
    (stakeFloorAt config x high (ck - (getCurrentEpoch x.state).toNat)) (ck - cz)
    (high + 2 - (getCurrentEpoch x.state).toNat) _ claim phi (by omega) (by omega) (by omega)
    (by omega) c.margin

/-- The least of a key's balance and the maximum, plus the debits, stays above the floor of the pin.

The state `p` lies on the climb, before its end `y`, so the key cannot yet have exited.

The least stake of the key is `2/3` of the maximum less the slashing quotient and the band. -/
private theorem Ctx.claimAt {g x z y p : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hz : Run config checks x z)
    (early : y.fork < .glamsterdam) (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (i : ℕ) (v0 : Validator) (found0 : z.state.validators.data[i]? = some v0)
    (unslashed0 : v0.slashed = false) (activated0 : v0.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (bal0 : preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt z i)
    (hystZ : effectiveAt z i ≤ actualBalanceAt z i + preset.downwardBand)
    (exitLate : ∀ (n : ForkedBeaconState preset) (_rest : Run config checks n y) (w : Validator),
      n.state.validators.data[i]? = some w → (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat)
    (rp : Run config checks z p) (rest : Run config checks p y)
    (lt : (getCurrentEpoch p.state).toNat < (getCurrentEpoch y.state).toNat) :
    ∃ events, rp.balanceEvents high = .ok events ∧
      2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
        preset.MAX_EFFECTIVE_BALANCE.toNat /
          (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        preset.downwardBand - 1 ≤ actualBalanceAt p i + keyDebits i events := by
  classical
  obtain ⟨m, rm, ins, eq, cm, hyst, events, replay, ih⟩ :=
    c.inv hz early within i v0 found0 unslashed0 activated0 bal0 hystZ exitLate rp rest
  have pEarly : p.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) early
  have mEarly : m.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps ins.chainSteps) pEarly
  have hm : Run config checks x m := hz.append rm
  obtain ⟨val, found, life⟩ := rm.registryLifecycle.validators i v0 found0
  have activated : val.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    rw [life.activationEpoch activated0]
    exact activated0
  have cmN : (getCurrentEpoch m.state).toNat = (getCurrentEpoch p.state).toNat :=
    congrArg UInt64.toNat cm
  have restEpoch := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest.chainSteps)
  obtain ⟨eins, hins⟩ := ins.balanceEvents_ok pEarly high
  have local_ : ins.balanceEvents (getCurrentEpoch m.state).toNat = .ok eins := by
    rw [← balanceEvents_eq_of_endpoint_le (high := high)
      (localHigh := (getCurrentEpoch m.state).toNat) ins (by omega) (by omega)]
    exact hins
  have exit' : ∀ w, p.state.validators.data[i]? = some w →
      (getCurrentEpoch m.state).toNat + 1 < w.exitEpoch.toNat := fun w hw => by
    have := exitLate p rest w hw
    omega
  have slashedCond := c.slashed_window hz rm mEarly i v0 val found0 found unslashed0
    (getCurrentEpoch p.state).toNat (by omega)
  have inside := Ctx.inside c hm ins pEarly cm.symm i val found activated exit' slashedCond hyst
    local_
  have charge := slashedCharge_run ins i val found
  have whole := balanceEvents_append rm ins high replay hins
  refine ⟨events ++ eins, by rw [eq]; exact whole, ?_⟩
  -- the arithmetic of the climb
  have xz := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps hz.chainSteps)
  have zm := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rm.chainSteps)
  have xEarly : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Nat.le_trans (fork_le_of_chainSteps hz.chainSteps)
      (Nat.le_trans (fork_le_of_chainSteps rm.chainSteps) (fork_le_of_chainSteps ins.chainSteps)))
      pEarly
  have e2 : min (actualBalanceAt m i) preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt p i +
      (keyDebits i eins + (if val.slashed = false ∧ ∃ w, p.state.validators.data[i]? = some w ∧
        w.slashed = true then newBq preset else 0)) := by
    have := inside
    unfold keyDebits
    unfold newBq
    simpa using this
  have step : min (actualBalanceAt m i) preset.MAX_EFFECTIVE_BALANCE.toNat +
      preset.downwardBand + keyDebits i events + slashedCharge preset m i ≤
      actualBalanceAt p i + preset.downwardBand + keyDebits i (events ++ eins) +
        slashedCharge preset p i := by
    rw [keyDebits_append, charge]
    omega
  have chargeLe : slashedCharge preset p i ≤ newBq preset := by
    unfold slashedCharge
    split <;> omega
  have h1 : 2 * (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) *
      stakeFloorAt config x high
        ((getCurrentEpoch p.state).toNat - (getCurrentEpoch x.state).toNat) ≤
      2 * (actualBalanceAt p i + preset.downwardBand +
        (keyDebits i (events ++ eins) + slashedCharge preset p i)) *
        stakeFloorAt config x high
          ((getCurrentEpoch z.state).toNat - (getCurrentEpoch x.state).toNat) +
      3 * (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) *
        ((getCurrentEpoch p.state).toNat - (getCurrentEpoch z.state).toNat) := by
    rw [← cmN]
    refine ih.trans ?_
    have := Nat.mul_le_mul_right (stakeFloorAt config x high
      ((getCurrentEpoch z.state).toNat - (getCurrentEpoch x.state).toNat))
      (Nat.mul_le_mul_left 2 step)
    have e : actualBalanceAt p i + preset.downwardBand + keyDebits i (events ++ eins) +
        slashedCharge preset p i = actualBalanceAt p i + preset.downwardBand +
          (keyDebits i (events ++ eins) + slashedCharge preset p i) := by omega
    rw [e] at this
    omega
  exact c.arith xEarly (getCurrentEpoch z.state).toNat (getCurrentEpoch p.state).toNat xz
    (by omega) (by omega) _ _ _ chargeLe h1

/-- A prefix of a list of events debits a key at most as much as the list. -/
private theorem keyDebits_le_of_prefix (i : ℕ) {a b : List (BalanceEvent preset)} (h : a <+: b) :
    keyDebits i a ≤ keyDebits i b := by
  obtain ⟨t, rfl⟩ := h
  rw [keyDebits_append]
  omega

/-- A state of the climb that precedes its end has the floor of the pin.

The debits are those of the run that contains it. -/
private theorem Ctx.floorRun {g x z y p w : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hz : Run config checks x z)
    (early : y.fork < .glamsterdam) (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (i : ℕ) (v0 : Validator) (found0 : z.state.validators.data[i]? = some v0)
    (unslashed0 : v0.slashed = false) (activated0 : v0.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (bal0 : preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt z i)
    (hystZ : effectiveAt z i ≤ actualBalanceAt z i + preset.downwardBand)
    (exitLate : ∀ (n : ForkedBeaconState preset) (_rest : Run config checks n y) (w : Validator),
      n.state.validators.data[i]? = some w → (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat)
    (rp : Run config checks z p) (rest : Run config checks p w) (restY : Run config checks p y)
    (lt : (getCurrentEpoch p.state).toNat < (getCurrentEpoch y.state).toNat)
    {Ef : List (BalanceEvent preset)} (hEf : (rp.append rest).balanceEvents high = .ok Ef) :
    2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
        preset.MAX_EFFECTIVE_BALANCE.toNat /
          (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        preset.downwardBand - 1 ≤ actualBalanceAt p i + keyDebits i Ef := by
  obtain ⟨events, replay, bound⟩ := c.claimAt hz early within i v0 found0 unslashed0 activated0
    bal0 hystZ exitLate rp restY lt
  obtain ⟨before, beforeOk, prefix_⟩ := Run.balanceEvents_prefix rp rest high Ef hEf
  rw [replay] at beforeOk
  cases beforeOk
  have := keyDebits_le_of_prefix i prefix_
  omega

/-- The end of the climb, the first state of the last epoch, has the floor of the pin too. -/
private theorem Ctx.claimEnd {g x z y zz n : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hz : Run config checks x z)
    (early : y.fork < .glamsterdam) (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (i : ℕ) (v0 : Validator) (found0 : z.state.validators.data[i]? = some v0)
    (unslashed0 : v0.slashed = false) (activated0 : v0.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (bal0 : preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt z i)
    (hystZ : effectiveAt z i ≤ actualBalanceAt z i + preset.downwardBand)
    (exitLate : ∀ (n : ForkedBeaconState preset) (_rest : Run config checks n y) (w : Validator),
      n.state.validators.data[i]? = some w → (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat)
    (pre0 : Run config checks z zz) (ok : advanceSlotAcross config checks zz = .ok n)
    (rest0 : Run config checks n y)
    (stepN : (getCurrentEpoch n.state).toNat = (getCurrentEpoch zz.state).toNat + 1)
    {Ef : List (BalanceEvent preset)}
    (hEf : (pre0.snoc (Step.slot ok)).balanceEvents high = .ok Ef) :
    2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
        preset.MAX_EFFECTIVE_BALANCE.toNat /
          (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        preset.downwardBand - 1 ≤ actualBalanceAt n i + keyDebits i Ef := by
  obtain ⟨m, rm, ins, eq, cm, hyst, claim⟩ := c.inv hz early within i v0 found0 unslashed0
    activated0 bal0 hystZ exitLate pre0 ((Run.nil.snoc (Step.slot ok)).append rest0)
  obtain ⟨claim', -⟩ := Ctx.inv_step c hz early within i v0 found0 unslashed0 activated0
    exitLate ok rest0 rm ins cm hyst claim stepN
  obtain ⟨events, replay, ineq⟩ := claim'
  have same : pre0.snoc (Step.slot ok) = rm.append (ins.snoc (Step.slot ok)) := by
    rw [eq]
    rfl
  rw [same, replay] at hEf
  cases hEf
  have nEarly : n.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest0.chainSteps) early
  have xz := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps hz.chainSteps)
  have zk := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps
    (pre0.snoc (Step.slot ok)).chainSteps)
  have xEarly : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Nat.le_trans (fork_le_of_chainSteps hz.chainSteps)
      (fork_le_of_chainSteps (pre0.snoc (Step.slot ok)).chainSteps)) nEarly
  have restEpoch := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest0.chainSteps)
  have chargeLe : slashedCharge preset n i ≤ newBq preset := by
    unfold slashedCharge
    split <;> omega
  have := c.arith xEarly (getCurrentEpoch z.state).toNat (getCurrentEpoch n.state).toNat xz zk
    (by omega) (min (actualBalanceAt n i) preset.MAX_EFFECTIVE_BALANCE.toNat) (keyDebits i Ef) _
    chargeLe
    (by
      have e : min (actualBalanceAt n i) preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
          (keyDebits i Ef + slashedCharge preset n i) =
          min (actualBalanceAt n i) preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
            keyDebits i Ef + slashedCharge preset n i := by omega
      rw [e]
      exact ineq)
  have := Nat.min_le_left (actualBalanceAt n i) preset.MAX_EFFECTIVE_BALANCE.toNat
  omega

/-- The state inside a slot step has the registry and the balances of the state after its upgrades.

The upgrades after Electra and before Gloas keep both. -/
private theorem mid_data {s n : ForkedBeaconState preset}
    (electra : .pectra ≤ s.fork) (early : n.fork < .glamsterdam)
    (upgrades : processUpgrades config checks s = .ok n) :
    n.state.validators.data = s.state.validators.data ∧
      n.state.balances.data = s.state.balances.data := by
  have target : .pectra ≤ n.fork := Nat.le_trans electra (processUpgrades_fork_le upgrades)
  obtain ⟨validators, balances, -⟩ := processUpgrades_retained_data electra early upgrades target
  exact ⟨validators, balances⟩

/-- Every state on the balance path of the climb has the key, and the floor of the pin. -/
private theorem Ctx.floors {g x z y zz n : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hz : Run config checks x z)
    (early : y.fork < .glamsterdam) (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (i : ℕ) (v0 : Validator) (found0 : z.state.validators.data[i]? = some v0)
    (unslashed0 : v0.slashed = false) (activated0 : v0.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (bal0 : preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt z i)
    (hystZ : effectiveAt z i ≤ actualBalanceAt z i + preset.downwardBand)
    (exitLate : ∀ (n : ForkedBeaconState preset) (_rest : Run config checks n y) (w : Validator),
      n.state.validators.data[i]? = some w → (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat)
    (pre0 : Run config checks z zz) (ok : advanceSlotAcross config checks zz = .ok n)
    (rest0 : Run config checks n y)
    (stepN : (getCurrentEpoch n.state).toNat = (getCurrentEpoch zz.state).toNat + 1)
    {Ef : List (BalanceEvent preset)}
    (hEf : (pre0.snoc (Step.slot ok)).balanceEvents high = .ok Ef) :
    ∀ p ∈ (pre0.snoc (Step.slot ok)).balancePath,
      (∃ val, p.state.validators.data[i]? = some val) ∧
        2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
          preset.MAX_EFFECTIVE_BALANCE.toNat /
            (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
          preset.downwardBand - 1 ≤ actualBalanceAt p i + keyDebits i Ef := by
  have nY := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest0.chainSteps)
  have nEarly : n.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest0.chainSteps) early
  -- a state of the run before the last step
  have runState : ∀ (p : ForkedBeaconState preset) (rp : Run config checks z p)
      (rest : Run config checks p zz), pre0 = rp.append rest →
      (∃ val, p.state.validators.data[i]? = some val) ∧
        2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
          preset.MAX_EFFECTIVE_BALANCE.toNat /
            (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
          preset.downwardBand - 1 ≤ actualBalanceAt p i + keyDebits i Ef := by
    intro p rp rest eq
    have pz := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest.chainSteps)
    obtain ⟨val, found, -⟩ := rp.registryLifecycle.validators i v0 found0
    refine ⟨⟨val, found⟩, ?_⟩
    refine c.floorRun hz early within i v0 found0 unslashed0 activated0 bal0 hystZ exitLate rp
      (rest.snoc (Step.slot ok)) ((rest.snoc (Step.slot ok)).append rest0) (by omega) ?_
    rw [eq] at hEf
    exact hEf
  intro p member
  simp only [Run.balancePath, List.mem_append] at member
  rcases member with member | member
  · rcases Run.mem_balancePath_split pre0 member with ⟨rp, rest, eq⟩ |
      ⟨q, n', rq, ok', rest, adv, eq, advOk, hp, upgrades⟩
    · exact runState p rp rest eq
    · have step := runState n' (rq.snoc (Step.slot ok')) rest eq
      have qFork : x.fork ≤ q.fork :=
        Nat.le_trans (fork_le_of_chainSteps hz.chainSteps) (fork_le_of_chainSteps rq.chainSteps)
      have n'Early : n'.fork < .glamsterdam :=
        Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps)
          (Nat.lt_of_le_of_lt (fork_le_of_chainSteps (Run.nil.snoc (Step.slot ok)).chainSteps)
            nEarly)
      have data := mid_data (config := config) (checks := checks) (s := ⟨q.fork, adv⟩)
        (Nat.le_trans c.electra qFork) n'Early upgrades
      subst hp
      obtain ⟨⟨val, found⟩, bound⟩ := step
      refine ⟨⟨val, ?_⟩, ?_⟩
      · simpa [data.1] using found
      · have : actualBalanceAt ⟨q.fork, adv⟩ i = actualBalanceAt n' i := by
          simp only [actualBalanceAt, data.2]
        rw [this]
        exact bound
  · obtain ⟨adv, advOk, upgrades⟩ := bind_ok_iff.mp ok
    simp only [Step.balancePath, advOk, Except.toOption, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl
    · exact runState _ pre0 .nil rfl
    · have zzFork : .pectra ≤ zz.fork := Nat.le_trans c.electra
        (Nat.le_trans (fork_le_of_chainSteps hz.chainSteps) (fork_le_of_chainSteps pre0.chainSteps))
      have data := mid_data (config := config) (checks := checks) (s := ⟨zz.fork, adv⟩) zzFork
        nEarly upgrades
      obtain ⟨val, found, -⟩ := (pre0.snoc (Step.slot ok)).registryLifecycle.validators i v0 found0
      refine ⟨⟨val, ?_⟩, ?_⟩
      · simpa [data.1] using found
      · have := c.claimEnd hz early within i v0 found0 unslashed0 activated0 bal0 hystZ exitLate
          pre0 ok rest0 stepN hEf
        have e : actualBalanceAt ⟨zz.fork, adv⟩ i = actualBalanceAt n i := by
          simp only [actualBalanceAt, data.2]
        rw [e]
        exact this
    · obtain ⟨val, found, -⟩ := (pre0.snoc (Step.slot ok)).registryLifecycle.validators i v0 found0
      exact ⟨⟨val, found⟩, c.claimEnd hz early within i v0 found0 unslashed0 activated0 bal0 hystZ
        exitLate pre0 ok rest0 stepN hEf⟩

end Epoch

/-- The last step of the floor of a new key, in naturals.

The effective balance is at least the least of three bounds.

It is therefore at least the stake of the pin, less the increment.

The debits are added back. -/
private theorem final_floor (A inc S effZ effN K : ℕ) (hA : A ≤ K) (hZ : K ≤ effZ)
    (h : min effZ (min K (A - 1 - S + 1 - inc)) ≤ effN) : A - inc ≤ effN + S := by
  rw [min_eq_right ((min_le_left _ _).trans hZ)] at h
  simp only [Nat.min_def] at h
  split_ifs at h <;> omega

/-! ## The effective balance of a new key -/

/-- A key that has an activation epoch two epochs ahead holds the largest effective balance there.

It is funded: its balance is at least its effective balance, which is at least the maximum.

Its effective balance is at most its balance and the downward band, and it is unslashed. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Run.funded_at_start {g x z :
  ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (aligned : MaxEffectiveBalancesAligned preset)
    (electra : .pectra ≤ x.fork) (pre : Run config checks x z) (zEarly : z.fork < .glamsterdam)
    (i : ℕ) {v0 : Validator} (found0 : z.state.validators.data[i]? = some v0)
    (actNeFar : v0.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (act : (getCurrentEpoch z.state).toNat + 2 = v0.activationEpoch.toNat) :
    v0.slashed = false ∧ preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt z i ∧
      effectiveAt z i ≤ actualBalanceAt z i + preset.downwardBand ∧
      preset.MAX_EFFECTIVE_BALANCE.toNat ≤ effectiveAt z i := by
  have electraZ : .pectra ≤ z.fork := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
  have actBound := v0.activationEpoch.toNat_lt
  have finite : getCurrentEpoch z.state < FAR_FUTURE_EPOCH :=
    UInt64.lt_iff_toNat_lt.mpr (by
      have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
      omega)
  have plusOne : (getCurrentEpoch z.state + 1).toNat = (getCurrentEpoch z.state).toNat + 1 := by
    rw [UInt64.toNat_add]
    have : (1 : UInt64).toNat = 1 := rfl
    rw [this]
    have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    exact Nat.mod_eq_of_lt (by omega)
  have lessAct : getCurrentEpoch z.state + 1 < v0.activationEpoch :=
    UInt64.lt_iff_toNat_lt.mpr (by rw [plusOne]; omega)
  obtain ⟨funded, maxLe, unslashed⟩ := (Internal.run_eligible_balance (shared.append pre) genesis
    caps.activation caps.compounding aligned zEarly finite).2 electraZ i v0 found0
    (Or.inl actNeFar)
    (UInt64.lt_iff_toNat_lt.mpr (by have := UInt64.lt_iff_toNat_lt.mp lessAct; omega))
  obtain ⟨bal, hbal, effLe⟩ := funded (by
    have := UInt64.lt_iff_toNat_lt.mp lessAct
    omega)
  refine ⟨unslashed, ?_, ?_, ?_⟩
  · have := UInt64.le_iff_toNat_le.mp (UInt64.le_trans maxLe effLe)
    simpa [actualBalanceAt, hbal] using this
  · have := UInt64.le_iff_toNat_le.mp effLe
    simp only [effectiveAt, actualBalanceAt, found0, hbal, Option.map_some, Option.getD_some]
    omega
  · have := UInt64.le_iff_toNat_le.mp maxLe
    simpa [effectiveAt, found0] using this

open DirectSafety.Apriori.Internal in
/-- A key created on the run keeps its effective balance near two thirds of the maximum.

Under the guard at the split, the key's effective balance at the end of the window is large.

It is at least two thirds of `MAX_EFFECTIVE_BALANCE`.

The bound loses the initial slashing penalty, the downward band and an increment.

The key's sync debits and its partial payments are added back.

The key is scheduled at the split.

It is not active by the epoch after the split, and it is active at the end. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Run.new_key_effective_floor {g x y
  : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : DirectSafety.Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (electra : .pectra ≤ x.fork) (fulu : .fusaka ≤ x.fork) (high : ℕ)
    (guard : DirectSafety.Apriori.aprioriGuardAt config x high)
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (window : preset.SeedLookaheadAtLeastThree)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (bands : preset.IncrementWithinUpwardBand) (facts : PinPresetFacts preset)
    (i : ℕ)
    (pending : ∀ v, x.state.validators.data[i]? = some v →
      (getCurrentEpoch x.state).toNat + 1 < v.activationEpoch.toNat)
    (active : isActiveAt y.state (getCurrentEpoch y.state) i = true)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
        preset.MAX_EFFECTIVE_BALANCE.toNat /
          (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        preset.downwardBand - preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      effectiveAt y i + (events.map (PinDrift.Internal.syncDebit i)).sum +
        (events.map (floorPartialDebit i.toUInt64)).sum := by
  -- The potential, the least of balance and maximum plus the band, follows the floor path.
  classical
  obtain ⟨wa, foundA, activeA⟩ := isActiveAt_eq_true_iff.mp active
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at activeA
  have exitGt := UInt64.lt_iff_toNat_lt.mp activeA.2
  have lowA := UInt64.le_iff_toNat_le.mp activeA.1
  obtain ⟨z, pre, post, v0, vy, split, found0, foundY, sameAct, actEq, actLe⟩ :=
    PinDrift.Internal.Run.start_state tail window i pending ⟨wa, foundA, fun far => by
      have := congrArg UInt64.toNat far
      have bound := wa.exitEpoch.toNat_lt
      have : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
      omega, activeA.1⟩ fun vy found => by
      obtain rfl := Option.some.inj (found.symm.trans foundA)
      omega
  obtain rfl := Option.some.inj (foundY.symm.trans foundA)
  have farToNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  have exitBound := vy.exitEpoch.toNat_lt
  have xz := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
  have zy := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
  have zEarly : z.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early
  have electraZ : .pectra ≤ z.fork := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
  have fuluZ : .fusaka ≤ z.fork := Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps)
  have actNeFar : v0.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    intro h
    rw [sameAct] at h
    have := congrArg UInt64.toNat h
    omega
  have actZ : (getCurrentEpoch z.state).toNat + 2 = v0.activationEpoch.toNat := by
    rw [sameAct]
    exact actEq
  obtain ⟨unslashed, bal0, hystZ, effZ⟩ :=
    PinDrift.Internal.Run.funded_at_start shared genesis caps aligned electra pre zEarly i found0
      actNeFar actZ
  have exitLate : ∀ (n : ForkedBeaconState preset) (_rest : Run config checks n y)
      (w : Validator), n.state.validators.data[i]? = some w →
      (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat := by
    intro n rest w found
    obtain ⟨later, foundL, life⟩ := rest.registryLifecycle.validators i w found
    have same : later = vy := Option.some.inj (foundL.symm.trans foundY)
    subst same
    by_cases assigned : w.exitEpoch = FAR_FUTURE_EPOCH
    · rw [assigned, farToNat]
      omega
    · rw [← life.exitEpoch assigned]
      exact exitGt
  obtain ⟨room, big⟩ := first_floor_of_guard shared genesis aligned (Nat.lt_of_le_of_lt
    (fork_le_of_chainSteps tail.chainSteps) early) electra guard facts
  have c : Ctx config checks g x high :=
    { shared := shared, genesis := genesis, parameters := parameters, caps := caps,
      aligned := aligned, twoSlots := twoSlots, electra := electra, fulu := fulu, guard := guard,
      delay := delay, vector := facts.vector, big := big, factor :=
        (PinDrift.Internal.PinPresetFacts.reward facts),
      quotientTwo := facts.quotient, margin := facts.margin, room := room,
      bands := bands }
  -- the last epoch starts with a slot step
  obtain ⟨zz, n, pre0, ok, rest0, splitPost, hzz, hn⟩ :=
    Run.cross_split post ((getCurrentEpoch y.state).toNat - 1) (by omega) (by omega)
  have nY := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest0.chainSteps)
  have nEarly : n.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest0.chainSteps) early
  obtain ⟨Ef, hEf⟩ := (pre0.snoc (Step.slot ok)).balanceEvents_ok nEarly high
  have floors := c.floors pre early within i v0 found0 unslashed actNeFar bal0 hystZ exitLate pre0
    ok rest0 (by omega) hEf
  -- the debits of the climb are debits of the run
  have tailEq : tail = (pre.append (pre0.snoc (Step.slot ok))).append rest0 := by
    rw [split, splitPost, Run.append_assoc]
  obtain ⟨ePre, hePre⟩ := pre.balanceEvents_ok (Nat.lt_of_le_of_lt (fork_le_of_chainSteps
    (pre0.snoc (Step.slot ok)).chainSteps) nEarly) high
  have whole := balanceEvents_append pre (pre0.snoc (Step.slot ok)) high hePre hEf
  rw [tailEq] at replayed
  obtain ⟨before, beforeOk, isPrefix⟩ := Run.balanceEvents_prefix
    (pre.append (pre0.snoc (Step.slot ok))) rest0 high events replayed
  rw [whole] at beforeOk
  cases beforeOk
  have debits : keyDebits i Ef ≤ keyDebits i events := by
    have := keyDebits_le_of_prefix i isPrefix
    rw [keyDebits_append] at this
    omega
  -- the balance floor along the climb, and the effective balance by hysteresis
  have nIn : i < z.state.validators.data.size := (Array.getElem?_eq_some_iff.mp found0).1
  have hBal := Run.effective_floor_of_balance_floor (pre0.snoc (Step.slot ok)) nEarly fuluZ
    (Nat.lt_of_lt_of_le (by norm_num) facts.incrementSize) i nIn
    (2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
        preset.MAX_EFFECTIVE_BALANCE.toNat /
          (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        preset.downwardBand - 1 - keyDebits i events) preset.MAX_EFFECTIVE_BALANCE.toNat
    (fun p member => by
      have := (floors p member).2
      omega)
    (fun p member => by
      obtain ⟨⟨val, found⟩, -⟩ := floors p member
      have := UInt64.le_iff_toNat_le.mp
        (Internal.minimum_cap caps.activation caps.compounding (h := p.fork) val)
      simpa [PinTerms.capAt, found] using this)
  have sameEff : effectiveAt y i = effectiveAt n i := by
    have inside : i < n.state.validators.data.size := by
      obtain ⟨val, found, -⟩ := (pre0.snoc (Step.slot ok)).registryLifecycle.validators i v0 found0
      exact (Array.getElem?_eq_some_iff.mp found).1
    exact run_same_epoch_effective rest0 early (UInt64.toNat_inj.mp (by omega)) i inside
  rw [sameEff]
  have kd : keyDebits i events = (events.map (PinDrift.Internal.syncDebit i)).sum +
      (events.map (floorPartialDebit i.toUInt64)).sum := rfl
  have fin := final_floor
    (2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
        preset.MAX_EFFECTIVE_BALANCE.toNat /
          (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        preset.downwardBand) preset.EFFECTIVE_BALANCE_INCREMENT.toNat (keyDebits i events)
    (effectiveAt z i) (effectiveAt n i) preset.MAX_EFFECTIVE_BALANCE.toNat
    ((Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (by omega))) effZ hBal
  omega

end PinKeys

end

end EthLib.Consensus.Models.Network


namespace EthLib.Consensus.Models.Network
namespace PinDrift

open Base Uint64 Models DirectSafety PinKeys
open DirectSafety.Apriori.Internal (recordBalance_single)

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-- `creditGain` is its part for compounding flows and its part for new keys past the cap. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.creditGain_split (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).creditGain =
      (pinTerms config state ancestor finalizedState).creditLow +
        (pinTerms config state ancestor finalizedState).creditCap := rfl

/-- `exitedRB` is the filter of `exitedR`.

It keeps the keys whose exit started on this branch after the split. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.exitedR_eq (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).exitedR =
      ∑ i ∈ (pinTerms config state ancestor finalizedState).positions with
        (pinTerms config state ancestor finalizedState).exitedRB i = true,
        (balanceAt state i + (pinTerms config state ancestor finalizedState).rise i) := rfl

/-- `slashedRB` is the filter of `slashedR`.

They are the keys slashed on this branch after the finalized epoch. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.slashedR_eq (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).slashedR =
      ((pinTerms config state ancestor finalizedState).positions.filter fun i =>
        (pinTerms config state ancestor finalizedState).slashedRB i = true).card := rfl

/-- The copy splits `queues` into its deposit part and its exit and consolidation part. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.queues_split (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).queues =
      (pinTerms config state ancestor finalizedState).queueDep +
        (pinTerms config state ancestor finalizedState).queueExit := rfl

/-- `queueRise` charges each key the queues let exit, at a band and the largest gain rate. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.queueRise_unfold (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).queueRise =
      if (pinTerms config state ancestor finalizedState).tight then 0 else
        3 * (pinTerms config state ancestor finalizedState).queueKeys *
          (preset.upwardBand + (pinTerms config state ancestor finalizedState).depth *
            (pinTerms config state ancestor finalizedState).gainRateMax) := rfl

/-- `queueKeys` counts the window's churn by `exitFloor`, the ends, the low keys and new keys. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.queueKeys_unfold (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).queueKeys =
      (pinTerms config state ancestor finalizedState).queueWindow /
          (pinTerms config state ancestor finalizedState).exitFloor + 2 +
        (pinTerms config state ancestor finalizedState).lowKeys +
        (pinTerms config state ancestor finalizedState).newKeySeats := rfl

/-- A key's fall is its effective balance less `floorC` within the delay, and all of it beyond. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.fall_eq (config : Config) (state
  ancestor finalizedState : BeaconState preset fork)
    (i : ℕ) :
    (pinTerms config state ancestor finalizedState).fall i =
      if (getCurrentEpoch state).toNat + 2 - (getCurrentEpoch finalizedState).toNat ≤
          config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat then
        balanceAt state i - (pinTerms config state ancestor finalizedState).floorC i
      else balanceAt state i := rfl

/-- `lowEB` takes the drops from the least of its starting balances, capped at activation. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.lowEB_unfold (config : Config)
    (state ancestor finalizedState : BeaconState preset fork)
    (i : ℕ) :
    (pinTerms config state ancestor finalizedState).lowEB i =
      min (min (min (balanceAt state i) (balanceAt finalizedState i))
            (((finalizedState.balances.data[i]?).map (·.toNat)).getD 0) -
          (pinTerms config state ancestor finalizedState).partialsDue i)
        preset.MIN_ACTIVATION_BALANCE.toNat -
        (pinTerms config state ancestor finalizedState).drop i := rfl

/-- `base0` of a key that the finalized block's state holds: its balance there, within its cap. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.base0_of_found (config : Config)
  (pulled anc fin : BeaconState preset fork)
    {i : ℕ} {val : Validator} (initial : fin.validators.data[i]? = some val) :
    (pinTerms config pulled anc fin).base0 i =
      min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i)
        (withdrawalMaxEffectiveBalance preset fork val).toNat := by
  simp only [pinTerms, PinTerms.capAt, initial, Option.map_some, Option.getD_some]
  rfl

/-- `drop` of a key that the finalized block's state holds, with its carry and its leak read out. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.drop_of_found (config : Config)
  (pulled anc fin : BeaconState preset fork)
    {i : ℕ} {val : Validator} (initial : fin.validators.data[i]? = some val) :
    (pinTerms config pulled anc fin).drop i =
      ((pinTerms config pulled anc fin).leakAt
          (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i -
            actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i + 1) +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          ((pinTerms config pulled anc fin).leakAt
            ((pinTerms config pulled anc fin).base0 i +
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i + 1) +
        preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  simp only [pinTerms, PinTerms.capAt, initial, Option.map_some, Option.getD_some]
  rfl

/-- `lowB` is the filter of `lowKeys`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.lowKeys_eq (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).lowKeys =
      ((pinTerms config state ancestor finalizedState).positions.filter fun i =>
        (pinTerms config state ancestor finalizedState).lowB i = true).card := rfl

/-! ## The setting of the pin -/

/-- The setting of the pin's drift bound for one call.

The call's own-epoch runs are left out. -/
structure Setting (config : Config) (checks : SignatureChecks) (g : ForkedBeaconState preset)
    (split fin pulled anc counted : BeaconState preset fork) (V : Finset ValidatorIndex) :
    Prop where
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
  shallow : (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat ≤
    config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  pulledTotal : ∃ t, getTotalActiveBalance pulled = .ok t
  facts : PinPresetFacts preset
  guard : DirectSafety.Apriori.aprioriGuardAt config ⟨fork, fin⟩ (getCurrentEpoch pulled).toNat
  finalized : anc.finalizedCheckpoint.epoch ≤ getCurrentEpoch split
  later : getCurrentEpoch pulled ≤ getCurrentEpoch counted
  near : (getCurrentEpoch counted).toNat ≤ (getCurrentEpoch pulled).toNat + 1
  voting : ∀ v ∈ V, v ∈ activeVoters pulled ∧ (slashedFlagAt counted v.toNat).getD false = false

/-- The call's epoch is at or after the split's, since a run leads from one to the other. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Setting.called {g :
  ForkedBeaconState preset}
    {split fin pulled anc counted : BeaconState preset fork} {V : Finset ValidatorIndex}
    (h : Setting config checks g split fin pulled anc counted V) :
    getCurrentEpoch split ≤ getCurrentEpoch pulled := by
  obtain ⟨toPulled⟩ := h.toPulled
  exact currentEpoch_le_of_chainSteps toPulled.chainSteps

/-- The withdrawal delay is positive, since it is at least the two epochs past the finalized one. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Setting.delay {g :
  ForkedBeaconState preset}
    {split fin pulled anc counted : BeaconState preset fork} {V : Finset ValidatorIndex}
    (h : Setting config checks g split fin pulled anc counted V) :
    0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨toPulled⟩ := h.toPulled
  have order : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch pulled).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps (fromFin.append toPulled).chainSteps)
  have := h.shallow
  omega

/-! ## Flows of the two branches -/

/-- The deposits applied to the key on R's branch.

They are over the replayed events of the run from the split. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.credDepR (events : List (BalanceEvent
  preset)) (v : ℕ) : ℕ :=
  ((events.filter (·.source = .deposits)).map (Internal.keyCredit v)).sum

/-- The consolidation credits to the key over the replayed events of a run.

It is the quantity that `Run.consolidation_credits_le_X_targets` bounds, summed over targets. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.consAmt (events : List (BalanceEvent
  preset)) (v : ℕ) : ℕ :=
  ((events.filter (·.source = .consolidations)).map (Internal.keyCredit v)).sum

/-! ### The C-side credits of a key, read from the run

They are read from the run itself, as `riseQ` is.

A block step's `.rewards` events are its proposer's credits.

A slot step's `.rewards` events are the epoch's flag rewards.

So a slot step counts only the sources named below.

Sync events are in `syncF` with the seats. -/

/-- Proposer and due-consolidation credits to the key on C's branch since the split.

The rounding slack of a credited key is `bandC`, once for each key.

The consolidation bands are not here: `bud_consolidations` charges them. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.propC {x y : ForkedBeaconState preset}
  (tail : Run config checks x y)
    (high v : ℕ) : ℕ :=
  (Internal.creditScan (fun s => decide (s = .rewards ∨ s = .consolidations))
    (fun s => decide (s = .consolidations)) v high tail)

/-- Proposer credits to the key on C's branch since the split, without the consolidation credits.

A credited stake compounds by at most a tenth.

The bounds of the terms charge an exact tenth of the keys' total, at ten times their terms.

The consolidation credits are under `consolidationsX`, so their compounding is not charged here. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.propN {x y : ForkedBeaconState preset}
  (tail : Run config checks x y)
    (high v : ℕ) : ℕ :=
  (Internal.creditScan (fun s => decide (s = .rewards)) (fun _ => false) v high tail)

/-- Proposer and deposit credits to the key on C's branch since the split.

They are `credC` without its consolidation credits.

A credited stake compounds by at most a tenth.

The bounds of the terms charge an exact tenth of the keys' total, at ten times their terms. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.credN {x y : ForkedBeaconState preset}
  (tail : Run config checks x y)
    (high v : ℕ) : ℕ :=
  (Internal.creditScan (fun s => decide (s = .rewards)) (fun s => decide (s = .deposits)) v high
    tail)

/-- The deposits credited to a key by events whose state before them does not hold it slashed.

A slashed key's whistleblower reward reads its effective balance at the slashing.

Of `credN`'s credits, only these deposits and its proposer credits can raise that balance.

This holds because a slashed key proposes no block. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.depPre (events : List (BalanceEvent
  preset)) (v : ℕ) : ℕ :=
  ((events.filter fun e => e.source = .deposits ∧
      ¬ (slashedFlagAt e.before.state v = some true)).map (Internal.keyCredit v)).sum

/-- Non-attestation credits to the key on C's branch since the split.

Whistleblower and sync credits are excluded.

The credits are the proposer's, deposits applied and consolidations.

The rounding slack of a credited key is `bandC`, once for each key. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.credC {x y : ForkedBeaconState preset}
  (tail : Run config checks x y)
    (high v : ℕ) : ℕ :=
  (Internal.creditScan (fun s => decide (s = .rewards ∨ s = .consolidations))
    (fun s => decide (s = .consolidations ∨ s = .deposits)) v high tail)

/-- Whistleblower credits to the key on C's branch since the split.

A whistleblower credit lands in the block of the proposer's own slot.

The rounding slack of a credited key is `bandC`, once for each key.

A slot step records only debits for a slashing. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.whistC {x y : ForkedBeaconState preset}
  (tail : Run config checks x y)
    (high v : ℕ) : ℕ :=
  (Internal.creditScan (fun s => decide (s = .slashings)) (fun _ => false) v high tail)

/-- The entries of X's queue of pending consolidations that name a target in `T`.

They are the ones that apply by `high + 1`.

It is the set of `Run.consolidation_credits_le_X_targets`, counted instead of summed. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.dueAt (X : BeaconState preset fork)
  (high : ℕ) (T : Finset ValidatorIndex) : ℕ :=
  if electra : .pectra ≤ fork then
    ((((X.pendingConsolidations electra).data.toList.filter fun c =>
        decide (c.targetIndex ∈ T)).filterMap fun c =>
      X.validators.data[c.sourceIndex.toNat]?).filter fun v =>
        !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)).length
  else 0

/-- The debit that one balance event takes from the key at position `i`. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.keyDebit (i : ℕ) (e : BalanceEvent
  preset) : ℕ :=
  actualBalanceAt e.before i - actualBalanceAt e.after i

/-- The sync-seat movement of the key over the replayed events of one run.

It is the key's credits and debits of the sync aggregates.

They are a seat's debit, a seat's reward, and the proposer's share of it.

The caller adds it over the two runs from the split, since both branches credit and debit seats. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.syncF (events : List (BalanceEvent
  preset)) (v : ℕ) : ℕ :=
  ((events.filter (·.source = .sync)).map (Internal.keyCredit v)).sum +
    ((events.filter (·.source = .sync)).map (Internal.keyDebit v)).sum

/-- One increment for a key slashed on R's branch after the finalized epoch.

The effective-balance drop of R's initial penalty is at most one increment, by `slashBand`.

`branchR` charges each such key the slash charge, at least one increment. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.slashR (t : PinTerms preset) (i : ℕ) :
  ℕ :=
  if t.slashedRB i = true then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0

/-- The gross credits to the key in the block steps of a run, from rewards, slashings and sync.

A block step counts the credits of its events from those sources, whatever the step takes back. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.grossScan (v high : ℕ) {x y :
  ForkedBeaconState preset} (tail : Run config checks x y) :
    ℕ :=
  (Internal.creditScan (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ =>
    false) v
    high tail)

/-- The gross credits of a run, after one more step. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.grossScan_snoc (v high : ℕ) {x m y
  : ForkedBeaconState preset}
    (pre : Run config checks x m) (step : Step config checks m y) :
    Internal.grossScan v high (pre.snoc step) = if (getCurrentEpoch m.state).toNat ≤ high + 1 then
      Internal.grossScan v high pre + Internal.stepCredit
        (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ => false) v step
      else Internal.grossScan v high pre := by
  unfold Internal.grossScan
  exact Internal.creditScan_snoc _ _ v high pre step

private theorem grossScan_slot_pos (i high : ℕ) {x m n : ForkedBeaconState preset}
    (pre : Run config checks x m) (ok : advanceSlotAcross config checks m = .ok n)
    (pos : 0 < Internal.grossScan i high (pre.snoc (Step.slot ok))) : 0 < Internal.grossScan i high
      pre := by
  rw [Internal.grossScan_snoc] at pos
  split at pos
  · simpa [Internal.stepCredit] using pos
  · exact pos

/-- The gross credits of a run add over `append`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.grossScan_append (v high : ℕ) {x m
  y : ForkedBeaconState preset}
    (pre : Run config checks x m) (post : Run config checks m y) :
    Internal.grossScan v high (pre.append post) = Internal.grossScan v high pre + Internal.grossScan
      v high post := by
  unfold Internal.grossScan
  exact Internal.creditScan_append _ _ v high pre post

/-- The rounding slack of a key with any C-side credit, once for each key.

The credits are the gross credits of its block steps, and an applied deposit.

A proposer reward, a whistleblower reward and a sync reward are block credits.

A consolidation credit is not here: `bud_consolidations` charges its band for each entry.

`credits` charges `upwardBand` for each credited key. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bandC {x y : ForkedBeaconState preset}
  (tail : Run config checks x y)
    (high v : ℕ) : ℕ :=
  if 0 < Internal.grossScan v high tail +
      (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v high tail) then
    preset.upwardBand else 0

/-- A sum over the members of a list that pass one of two apart tests is the two sums. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.sum_filter_or {α : Type} (L : List
  α) (p q : α → Bool)
    (apart : ∀ a, ¬ (p a = true ∧ q a = true)) (f : α → ℕ) :
    ((L.filter fun a => p a || q a).map f).sum =
      ((L.filter p).map f).sum + ((L.filter q).map f).sum := by
  induction L with
  | nil => simp
  | cons a rest ih =>
    by_cases hp : p a = true
    · have hq : q a = false := by
        cases h : q a
        · rfl
        · exact absurd ⟨hp, h⟩ (apart a)
      simp [hp, hq, ih]; omega
    · by_cases hq : q a = true
      · simp [hp, hq, ih]; omega
      · simp [hp, hq, ih]

/-- The credits of a run that a scan reads add over two apart sets of sources.

The block sources of the scan and the slot sources are each the union of two apart sources. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.creditScan_or (blockP slotP b₁ b₂
  s₁ s₂ : BalanceSource → Bool)
    (hb : ∀ s, blockP s = (b₁ s || b₂ s)) (hs : ∀ s, slotP s = (s₁ s || s₂ s))
    (apartB : ∀ s, ¬ (b₁ s = true ∧ b₂ s = true)) (apartS : ∀ s, ¬ (s₁ s = true ∧ s₂ s = true))
    (v high : ℕ) {x y : ForkedBeaconState preset} (tail : Run config checks x y) :
    (Internal.creditScan blockP slotP v high tail) =
      (Internal.creditScan b₁ s₁ v high tail) + (Internal.creditScan b₂ s₂ v high tail) := by
  obtain rfl : blockP = fun s => b₁ s || b₂ s := funext hb
  obtain rfl : slotP = fun s => s₁ s || s₂ s := funext hs
  induction tail with
  | nil => rfl
  | @snoc middle last pre step ih =>
    have split : Internal.stepCredit (fun s => b₁ s || b₂ s) (fun s => s₁ s || s₂ s) v step =
        Internal.stepCredit b₁ s₁ v step + Internal.stepCredit b₂ s₂ v step := by
      cases step with
      | slot ok =>
        simp only [Internal.stepCredit]
        exact Internal.sum_filter_or _ (fun e : BalanceEvent preset => s₁ e.source)
          (fun e => s₂ e.source) (fun e => apartS e.source) _
      | block engine signed due ok =>
        simp only [Internal.stepCredit]
        exact Internal.sum_filter_or _ (fun e : BalanceEvent preset => b₁ e.source)
          (fun e => b₂ e.source) (fun e => apartB e.source) _
    rw [Internal.creditScan_snoc, Internal.creditScan_snoc, Internal.creditScan_snoc, split]
    split_ifs <;> omega

/-- The credits of a key on C's branch are its proposer credits and the deposits it is credited. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.credN_split {x y :
  ForkedBeaconState preset} (tail : Run config checks x y)
    (high v : ℕ) :
    Internal.credN tail high v = Internal.propN tail high v +
      (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v high tail) :=
  Internal.creditScan_or _ _ (fun s => decide (s = .rewards)) (fun _ => false) (fun _ => false)
    (fun s => decide (s = .deposits)) (fun s => by cases s <;> decide)
    (fun s => by cases s <;> decide)
    (fun s h => by simp at h) (fun s h => by simp at h) v high tail

/-- The credits of a key with the consolidations are its `credN` and its consolidation credits. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.credC_split {x y :
  ForkedBeaconState preset} (tail : Run config checks x y)
    (high v : ℕ) :
    Internal.credC tail high v = Internal.credN tail high v +
      (Internal.creditScan (fun s => decide (s = .consolidations))
        (fun s => decide (s = .consolidations)) v high tail) :=
  Internal.creditScan_or _ _ (fun s => decide (s = .rewards)) (fun s => decide (s =
    .consolidations))
    (fun s => decide (s = .deposits)) (fun s => decide (s = .consolidations))
    (fun s => by cases s <;> decide) (fun s => by cases s <;> decide)
    (fun s h => by simp at h; exact absurd (h.1.symm.trans h.2) (by decide))
    (fun s h => by simp at h; exact absurd (h.1.symm.trans h.2) (by decide)) v high tail

/-- The proposer credits with the consolidations are `propN` and the consolidation credits. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.propC_split {x y :
  ForkedBeaconState preset} (tail : Run config checks x y)
    (high v : ℕ) :
    Internal.propC tail high v = Internal.propN tail high v +
      (Internal.creditScan (fun s => decide (s = .consolidations))
        (fun s => decide (s = .consolidations)) v high tail) :=
  Internal.creditScan_or _ _ (fun s => decide (s = .rewards)) (fun s => decide (s =
    .consolidations))
    (fun _ => false) (fun s => decide (s = .consolidations))
    (fun s => by cases s <;> decide) (fun s => by cases s <;> decide)
    (fun s h => by simp at h; exact absurd (h.1.symm.trans h.2) (by decide))
    (fun s h => by simp at h) v high tail

/-- The proposer credits of two runs, one after the other, add. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.propN_append {x m y :
  ForkedBeaconState preset} (pre : Run config checks x m)
    (post : Run config checks m y) (high v : ℕ) :
    Internal.propN (pre.append post) high v = Internal.propN pre high v + Internal.propN post high v
      :=
  Internal.creditScan_append _ _ v high pre post

/-- The gain of `C` credited gwei over `depth` epochs, at the reward rate `P`.

The credits count in whole increments rounded up, and each epoch's gain is rounded down. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.gainOn (preset : Preset) (depth P C :
  ℕ) : ℕ :=
  depth * ((((C + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) /
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * P *
    (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) / WEIGHT_DENOMINATOR.toNat)

/-- The rounding slack of a key whose balance on R's branch took a sync debit that `high` omits.

It is one increment and the downward band less one.

`branchR` charges that step for each of its keys. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bandR (events : List (BalanceEvent
  preset)) (v : ℕ) : ℕ :=
  if 0 < ((events.filter (·.source = .sync)).map (Internal.keyDebit v)).sum then
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1 else 0

/-- The sync credits to the key over the replayed events of one run. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.syncCr (events : List (BalanceEvent
  preset)) (v : ℕ) : ℕ :=
  (events.map (Internal.syncCredit v)).sum

/-- The sync debits of the key over the replayed events of one run. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.syncD (events : List (BalanceEvent
  preset)) (v : ℕ) : ℕ :=
  (events.map (Internal.syncDebit v)).sum

/-- A whistleblower's share of an amount at eleven tenths of three, rounded up.

It is `⌈33·x/(10·WRQ)⌉`, with the whistleblower quotient of the fork. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.wShare (preset : Preset) (fork : Fork)
  (x : ℕ) : ℕ :=
  (33 * x + 10 * (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
    (10 * (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)

/-- The band of each due consolidation entry of the state `X` that targets the key. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bandX (X : BeaconState preset fork)
  (high v : ℕ) : ℕ :=
  preset.upwardBand * Internal.dueAt X high {UInt64.ofNat v}

/-- The initial slashing penalty of a key slashed on R's branch after the split, at the cap. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.slashW (t : PinTerms preset) (i : ℕ) :
  ℕ :=
  if t.slashedRB i = true then
    preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
      (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat
  else 0

/-- The leak a key's sync debits on R's run from the finalized block induce above `ebUp`.

It is the leak at the largest effective balance on the run, less the leak at `ebUp`.

`inducedR` is 0 when the key's withdrawable epoch at R is at most R's epoch plus one.

Such a key is swept by R, so the leak is not charged. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.inducedR (t : PinTerms preset) {x y :
  ForkedBeaconState preset}
    (tail : Run config checks x y) (i : ℕ) : ℕ :=
  if t.withdrawnRB i = true then 0
  else
    t.depthFin * (t.leakAt ((tail.balancePath.map fun z => effectiveAt z i).foldl max 0) i -
      t.leakAt (t.ebUp i) i)

/-- A key that R holds withdrawable by the next epoch has no induced leak. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.inducedR_of_withdrawn (t : PinTerms
  preset) {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (i : ℕ) (withdrawn : t.withdrawnRB i = true) :
    Internal.inducedR t tail i = 0 := by
  simp [Internal.inducedR, withdrawn]

/-- A key that R does not hold withdrawable is charged the leak at its largest balance. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.inducedR_of_not_withdrawn (t :
  PinTerms preset) {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (i : ℕ) (kept : t.withdrawnRB i = false) :
    Internal.inducedR t tail i =
      t.depthFin * (t.leakAt ((tail.balancePath.map fun z => effectiveAt z i).foldl max 0) i -
        t.leakAt (t.ebUp i) i) := by
  simp [Internal.inducedR, kept]

/-- The flows that can raise a key's balance on C above R's base, besides its epoch rewards.

They are its credits on C's branch and its sync debits on R's branch and on the shared segment.

They also include the initial penalty of a slashing on R's branch.

The credits `cred` default to `credC`, which counts the key's deposits.

A key of `K5` passes `propC`, which does not. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.flowCredit (t : PinTerms preset) {x y :
  ForkedBeaconState preset}
    (tailC : Run config checks x y) (high : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (i : ℕ)
    (cred : ℕ := Internal.credC tailC high i) : ℕ :=
  cred + Internal.whistC tailC high i + Internal.syncCr eventsC i + Internal.syncD events i +
    Internal.syncD eventsF i +
    Internal.slashW t i

/-- The gain of a key's flows over the window, at eleven tenths in whole increments.

It is one floor of all the flows; the closure splits it by kind in aggregate.

Its rate is floored once, after the increments, as the gain of the credits is.

A gain-carrying run starts at the split, so the gain runs over at most the shorter window. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.flowGain (t : PinTerms preset) {x y :
  ForkedBeaconState preset}
    (tailC : Run config checks x y) (high : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (i : ℕ)
    (cred : ℕ := Internal.credC tailC high i) : ℕ :=
  min t.depth t.depthFin * (11 * Internal.flowCredit t tailC high eventsC events eventsF i cred /
    (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * t.perIncrement *
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat)

/-- The flow gain of a key whose rise is on its kept arm, or that R's registry does not hold.

On the other arm the rise is the key's whole headroom, which holds its gains already.

A key that R's registry does not hold is charged here only in the low regime.

In the high regime `creditCap` charges it up to the cap. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.flowK (t : PinTerms preset) {x y :
  ForkedBeaconState preset}
    (tailC : Run config checks x y) (high : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (i : ℕ)
    (cred : ℕ := Internal.credC tailC high i) : ℕ :=
  if t.keptArm i = true ∨ (i ∉ t.positions ∧ t.gainHigh = false) then
    Internal.flowGain t tailC high eventsC events eventsF i cred
  else 0

/-- One unit of gain for a key with any flow.

A flow can raise the key's effective balance by one more increment than its rewards alone. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.unitK (t : PinTerms preset) {x y :
  ForkedBeaconState preset}
    (tailC : Run config checks x y) (high : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (i : ℕ)
    (cred : ℕ := Internal.credC tailC high i) : ℕ :=
  if 0 < Internal.flowCredit t tailC high eventsC events eventsF i cred then t.unitGain else 0

/-- The terms of a key's rise that the third window adds.

They are its sync debits on the shared segment, its flow gain and its unit.

They also include the leak that its sync debits on R's branch induce.

`bud_sync`, `flow_split_of`, `bud_units` and `bud_syncLeak` pay them, in that order. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.keyExtra (t : PinTerms preset) {x y :
  ForkedBeaconState preset}
    (tail : Run config checks x y) {x' y' : ForkedBeaconState preset}
    (tailC : Run config checks x' y') (high : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (i : ℕ)
    (cred : ℕ := Internal.credC tailC high i) : ℕ :=
  Internal.syncD eventsF i + Internal.flowK t tailC high eventsC events eventsF i cred +
    Internal.unitK t tailC high eventsC events eventsF i cred + Internal.inducedR t tail i

/-- A quantity of the sync events, summed over all events with the others at zero. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.sum_map_sync (events : List
  (BalanceEvent preset))
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
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.sum_syncDebit_eq (events : List
  (BalanceEvent preset)) (v : ℕ) :
    (events.map (Internal.syncDebit v)).sum =
      ((events.filter (·.source = .sync)).map (Internal.keyDebit v)).sum :=
  Internal.sum_map_sync events (Internal.keyDebit v)

/-- The rounding band of a key is the band if the key has a sync debit, and zero otherwise. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bandR_eq (events : List
  (BalanceEvent preset)) (v : ℕ) :
    Internal.bandR events v = if 0 < (events.map (Internal.syncDebit v)).sum then
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1 else 0 := by
  unfold Internal.bandR
  rw [← Internal.sum_syncDebit_eq]

/-- A key's credit in an event is at most the event's credit limit. -/
private theorem keyCredit_le_creditLimit (i : ℕ) (e : BalanceEvent preset)
    (bounded : e.credits ≤ e.creditLimit) : Internal.keyCredit i e ≤ e.creditLimit := by
  refine le_trans ?_ bounded
  unfold Internal.keyCredit
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
      obtain ⟨_, _, _, _, events⟩ := recordBalance_single ok'
      rw [events]
      intro e member source
      rcases List.mem_append.mp member with old | new
      · exact held' e old source
      · obtain rfl := List.mem_singleton.mp new
        exact absurd source (by simp)
    · intro src pre' post' index penalty pen held' ok'
      obtain ⟨_, _, _, _, events⟩ := recordBalance_single ok'
      rw [events]
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
  case pendingDeposits | pendingConsolidations =>
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
    ∀ e ∈ events, Internal.keyCredit i e ≤
      (if e.source = .rewards ∨ e.source = .consolidations then Internal.keyCredit i e else 0) +
        (if e.source = .slashings then Internal.keyCredit i e else 0) + Internal.syncCredit i e :=
          by
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
  · simp [sy, Internal.syncCredit, Internal.keyCredit]
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
    ∀ e ∈ events, e.source ≠ .rewards → Internal.keyCredit i e ≤
      (if e.source = .consolidations ∨ e.source = .deposits then Internal.keyCredit i e else 0) +
        Internal.syncCredit i e := by
  intro e member notRewards
  obtain ⟨-, positive⟩ := Step.balanceEvents_credit_sources (Step.slot ok) early
    (run_justified_separated shared genesis).1 replayed e member
  have limit := keyCredit_le_creditLimit i e (bounded e member)
  by_cases cd : e.source = .consolidations ∨ e.source = .deposits
  · simp [cd]
  by_cases sy : e.source = .sync
  · simp [sy, Internal.syncCredit, Internal.keyCredit]
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

/-- The credits of a block step to a key are within those of `credC`, `whistC` and sync. -/
private theorem block_credit_split {g : ForkedBeaconState preset} {fork : Fork}
    {s t : BeaconState preset fork} {engine : ExecutionEngine preset fork}
    {signed : SignedBeaconBlock preset fork} {due : upgradeDue config ⟨fork, s⟩ = false}
    {ok : applySignedBlock config checks engine s signed true = .ok t}
    (shared : Run config checks g ⟨fork, s⟩) (genesis : Genesis config checks g)
    (early : fork < .glamsterdam) (electra : .pectra ≤ fork) (i : ℕ)
    {events : List (BalanceEvent preset)}
    (replayed : (Step.block engine signed due ok).balanceEvents = .ok events)
    (bounded : ∀ e ∈ events, e.credits ≤ e.creditLimit) :
    (events.map (Internal.keyCredit i)).sum ≤
      ((events.filter fun x => decide (x.source = .rewards ∨ x.source = .consolidations)).map
        (Internal.keyCredit i)).sum +
      ((events.filter fun x => decide (x.source = .slashings)).map (Internal.keyCredit i)).sum +
      (events.map (Internal.syncCredit i)).sum := by
  have each := block_event_credit shared genesis early electra i replayed bounded
  simpa using sum_credits_split events (Internal.keyCredit i) (Internal.syncCredit i) (fun _ =>
    true)
    (fun s => decide (s = .rewards ∨ s = .consolidations)) (fun s => decide (s = .slashings))
    (fun e m _ => by simpa using each e m)

/-- The slot credits of a step to a key, other than rewards, fit consolidations, deposits, sync. -/
private theorem slot_credit_split {g m n : ForkedBeaconState preset}
    {ok : advanceSlotAcross config checks m = .ok n}
    (shared : Run config checks g m) (genesis : Genesis config checks g)
    (early : n.fork < .glamsterdam) (i : ℕ) {events : List (BalanceEvent preset)}
    (replayed : (Step.slot ok).balanceEvents = .ok events)
    (bounded : ∀ e ∈ events, e.credits ≤ e.creditLimit) :
    ((events.filter fun x => decide (x.source ≠ .rewards)).map (Internal.keyCredit i)).sum ≤
      ((events.filter fun x => decide (x.source = .consolidations ∨ x.source = .deposits)).map
        (Internal.keyCredit i)).sum +
      ((events.filter fun _ => false).map (Internal.keyCredit i)).sum + (events.map
        (Internal.syncCredit i)).sum := by
  have each := slot_event_credit shared genesis early i replayed bounded
  exact sum_credits_split events (Internal.keyCredit i) (Internal.syncCredit i)
    (fun s => decide (s ≠ .rewards)) (fun s => decide (s = .consolidations ∨ s = .deposits))
    (fun _ => false) (fun e m notRewards => by simpa using each e m (by simpa using notRewards))

/-- The events of a step are within their credit limits. -/
private theorem step_events_bounded {g m n : ForkedBeaconState preset}
    (shared : Run config checks g m) (genesis : Genesis config checks g)
    (step : Step config checks m n) (early : n.fork < .glamsterdam)
    {events : List (BalanceEvent preset)} (ok : step.balanceEvents = .ok events) :
    ∀ e ∈ events, e.credits ≤ e.creditLimit := by
  have run := DirectSafety.Apriori.Internal.single_balanceEvents step ok
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
    Internal.stepCredit (fun _ => true) (fun _ => true) i step ≤
      Internal.stepCredit (fun s => decide (s = .rewards ∨ s = .consolidations))
        (fun s => decide (s = .consolidations ∨ s = .deposits)) i step +
      Internal.stepCredit (fun s => decide (s = .slashings)) (fun _ => false) i step +
      (events.map (Internal.syncCredit i)).sum := by
  have bounded := step_events_bounded shared genesis step early replayed
  cases step with
  | block engine signed due ok =>
    have split := block_credit_split shared genesis early electra i replayed bounded
    simp only [Internal.stepCredit, replayed, Except.toOption, Option.getD_some, List.filter_true]
      at split ⊢
    exact split
  | slot ok => exact absurd rfl (notSlot ok)

/-- The credits of a block step to a key are at most its gross credits.

A block step has no consolidation event, and its other sources credit nothing.

The step counts all its credits on the left.

On the right it counts only those of rewards, slashings and sync. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.block_credit_le_gross {g :
  ForkedBeaconState preset} {f : Fork}
    {s t : BeaconState preset f} {engine : ExecutionEngine preset f}
    {signed : SignedBeaconBlock preset f} {due : upgradeDue config ⟨f, s⟩ = false}
    {ok : applySignedBlock config checks engine s signed true = .ok t}
    (shared : Run config checks g ⟨f, s⟩) (genesis : Genesis config checks g)
    (early : f < .glamsterdam) (electra : .pectra ≤ f) (i : ℕ) :
    Internal.stepCredit (fun _ => true) (fun _ => true) i (Step.block engine signed due ok) ≤
      Internal.stepCredit (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ =>
        false) i
        (Step.block engine signed due ok) := by
  obtain ⟨events, replayed⟩ := (Step.block engine signed due ok :
    Step config checks ⟨f, s⟩ ⟨f, t⟩).balanceEvents_ok early
  have bounded := step_events_bounded shared genesis (Step.block engine signed due ok) early
    replayed
  have noCons := blockReplay_noConsolidations electra early engine s signed.message
    (Step.balanceEvents_block early replayed)
  have split : (events.map (Internal.keyCredit i)).sum ≤ ((events.filter fun e => decide
      (e.source = .rewards ∨ e.source = .slashings ∨ e.source = .sync)).map (Internal.keyCredit
        i)).sum := by
    simpa using sum_credits_split events (Internal.keyCredit i) (fun _ => 0) (fun _ => true)
      (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ => false)
      fun e member _ => by
        have each := block_event_credit shared genesis early electra i replayed bounded e member
        by_cases kept : e.source = .rewards ∨ e.source = .slashings ∨ e.source = .sync
        · simp [kept]
        · simp only [not_or] at kept
          simp [kept.1, kept.2.1, kept.2.2, noCons e member, Internal.syncCredit] at each ⊢
          omega
  simp only [Internal.stepCredit, replayed, Except.toOption, Option.getD_some]
  simpa using split

/-- A block step raises the balance of a key by at most its gross credits. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.block_balance_le_gross {g :
  ForkedBeaconState preset} {f : Fork}
    {s t : BeaconState preset f} {engine : ExecutionEngine preset f}
    {signed : SignedBeaconBlock preset f} {due : upgradeDue config ⟨f, s⟩ = false}
    {ok : applySignedBlock config checks engine s signed true = .ok t}
    (shared : Run config checks g ⟨f, s⟩) (genesis : Genesis config checks g)
    (early : f < .glamsterdam) (electra : .pectra ≤ f) (i : ℕ) :
    actualBalanceAt (⟨f, t⟩ : ForkedBeaconState preset) i ≤
      actualBalanceAt (⟨f, s⟩ : ForkedBeaconState preset) i + Internal.stepCredit
        (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ => false) i
        (Step.block engine signed due ok) := by
  obtain ⟨events, replayed⟩ := (Step.block engine signed due ok :
    Step config checks ⟨f, s⟩ ⟨f, t⟩).balanceEvents_ok early
  have base := Internal.step_balance_le_events (Step.block engine signed due ok :
    Step config checks ⟨f, s⟩ ⟨f, t⟩) early i replayed
  have credit := Internal.block_credit_le_gross (due := due) (ok := ok) shared genesis early electra
    i
  simp only [Internal.stepCredit, replayed, Except.toOption, Option.getD_some,
    List.filter_true] at credit ⊢
  omega

/-- The credits of a step, net for a block step, are at most those of `credC`, `whistC` and sync. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.step_credit_le_sources {g m n :
  ForkedBeaconState preset}
    (shared : Run config checks g m) (genesis : Genesis config checks g)
    (step : Step config checks m n) (early : n.fork < .glamsterdam) (electra : .pectra ≤ m.fork)
    (i : ℕ) {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events) :
    Internal.stepNet i step + Internal.stepCredit (fun _ => false) (fun s => decide (s ≠ .rewards))
      i step ≤
      Internal.stepCredit (fun s => decide (s = .rewards ∨ s = .consolidations))
        (fun s => decide (s = .consolidations ∨ s = .deposits)) i step +
      Internal.stepCredit (fun s => decide (s = .slashings)) (fun _ => false) i step +
      (events.map (Internal.syncCredit i)).sum := by
  have bounded := step_events_bounded shared genesis step early replayed
  have base := Internal.step_balance_le_events step early i replayed
  cases step with
  | block engine signed due ok =>
    have split := block_credit_le_sources shared genesis (Step.block engine signed due ok)
      (by intro ok' h; cases h) early electra i replayed
    simp only [Internal.stepNet, Internal.stepCredit, replayed, Except.toOption, Option.getD_some,
      sum_filter_none, List.filter_true] at base split ⊢
    omega
  | slot ok =>
    have split := slot_credit_split shared genesis early i replayed bounded
    simp only [Internal.stepNet, Internal.stepCredit, replayed, Except.toOption, Option.getD_some,
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
    Internal.stepCredit (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ =>
      false) i
        step + Internal.stepCredit (fun _ => false) (fun s => decide (s ≠ .rewards)) i step ≤
      Internal.stepCredit (fun s => decide (s = .rewards ∨ s = .consolidations))
        (fun s => decide (s = .consolidations ∨ s = .deposits)) i step +
      Internal.stepCredit (fun s => decide (s = .slashings)) (fun _ => false) i step +
      (events.map (Internal.syncCredit i)).sum ∧
    Internal.stepNet i step ≤ Internal.stepCredit
      (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ => false) i step ∧
    Internal.stepCredit (fun _ => false) (fun s => decide (s ≠ .rewards)) i step ≤
      Internal.stepCredit (fun _ => false)
        (fun s => decide (s = .consolidations ∨ s = .deposits)) i step := by
  have bounded := step_events_bounded shared genesis step early replayed
  cases step with
  | block engine signed due ok =>
    have split := block_credit_split shared genesis early electra i replayed bounded
    have gross := Internal.block_balance_le_gross (engine := engine) (signed := signed) (due := due)
      (ok := ok) shared genesis early electra i
    have part : ((events.filter fun x => decide
        (x.source = .rewards ∨ x.source = .slashings ∨ x.source = .sync)).map (Internal.keyCredit
          i)).sum ≤
        (events.map (Internal.keyCredit i)).sum :=
      (((List.filter_sublist).map _).sum_le_sum fun _ _ => Nat.zero_le _)
    simp only [Internal.stepNet, Internal.stepCredit, replayed, Except.toOption, Option.getD_some,
      sum_filter_none] at gross part split ⊢
    omega
  | slot ok =>
    have split := slot_credit_split shared genesis early i replayed bounded
    have zero := (Internal.slot_syncDebit_zero electra ok early replayed i).2
    simp only [Internal.stepNet, Internal.stepCredit, replayed, Except.toOption, Option.getD_some,
      sum_filter_none] at split ⊢
    omega

/-- The credits of a run, gross for its block steps, are at most those of `credC`, `whistC`, sync.

A block step's net rise is within its gross credits, so the net credits of the run are too.

Its slot credits other than epoch rewards are at most those of consolidations and deposits. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.credits_le_sources {g x y :
  ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis config checks g)
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) (electra : .pectra ≤ x.fork)
    (i high : ℕ) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events) :
    Internal.grossScan i high tail + (Internal.creditScan (fun _ => false) (fun s => decide (s ≠
      .rewards)) i high
      tail) ≤ Internal.credC tail high i + Internal.whistC tail high i + (events.map
        (Internal.syncCredit i)).sum ∧
    Internal.netScan i high tail ≤ Internal.grossScan i high tail ∧
    (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high tail) ≤
      (Internal.creditScan (fun _ => false)
        (fun s => decide (s = .consolidations ∨ s = .deposits)) i high tail) := by
  induction tail generalizing events with
  | nil =>
    simp only [Run.balanceEvents, pure, Except.pure, Except.ok.injEq] at replayed
    subst replayed
    simp [Internal.credC, Internal.whistC, Internal.grossScan, Internal.netScan_nil,
      Internal.creditScan_nil]
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
      unfold Internal.credC Internal.whistC Internal.grossScan at previous ⊢
      unfold Internal.grossScan at previousNet
      simp only [Internal.netScan_snoc, Internal.creditScan_snoc, selected, ↓reduceIte,
        List.map_append,
        List.sum_append]
      exact ⟨by omega, by omega, by omega⟩
    · simp only [selected, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at rest
      obtain rfl := rest
      unfold Internal.credC Internal.whistC Internal.grossScan at previous ⊢
      unfold Internal.grossScan at previousNet
      simp only [Internal.netScan_snoc, Internal.creditScan_snoc, selected, ↓reduceIte]
      exact ⟨previous, previousNet, previousSlot⟩

/-- The credits of a switch step, whole, and of the runs around it are at most the sources.

The credits before the step are read net, and then gross. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.flip_credits_le_sources {g x s s' y
  : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis config checks g)
    (pre : Run config checks x s) (step : Step config checks s s') (post : Run config checks s' y)
    (notSlot : ∀ ok, step ≠ Step.slot ok) (early : y.fork < .glamsterdam)
    (electra : .pectra ≤ x.fork) (i high : ℕ) (inside : (getCurrentEpoch s.state).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)}
    (replayed : ((pre.snoc step).append post).balanceEvents high = .ok events) :
    (Internal.netScan i high pre + (Internal.creditScan (fun _ => false) (fun s => decide (s ≠
      .rewards)) i high
        pre) + Internal.stepCredit (fun _ => true) (fun _ => true) i step +
      (Internal.netScan i high post + (Internal.creditScan (fun _ => false) (fun s => decide (s ≠
        .rewards)) i high
        post)) ≤ Internal.credC ((pre.snoc step).append post) high i +
      Internal.whistC ((pre.snoc step).append post) high i + (events.map (Internal.syncCredit
        i)).sum) ∧
    (Internal.grossScan i high pre + (Internal.creditScan (fun _ => false) (fun s => decide (s ≠
      .rewards)) i high
        pre) + Internal.stepCredit (fun _ => true) (fun _ => true) i step +
      (Internal.netScan i high post + (Internal.creditScan (fun _ => false) (fun s => decide (s ≠
        .rewards)) i high
        post)) ≤ Internal.credC ((pre.snoc step).append post) high i +
      Internal.whistC ((pre.snoc step).append post) high i + (events.map (Internal.syncCredit
        i)).sum) := by
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
  have first := Internal.credits_le_sources shared genesis pre sEarly electra i high replayed1
  have last := Internal.credits_le_sources (shared.append (pre.snoc step)) genesis post early
    (Nat.le_trans electra (fork_le_of_chainSteps (pre.snoc step).chainSteps)) i high replayed2
  have middle := block_credit_le_sources (shared.append pre) genesis step notSlot s'Early
    (Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)) i replayedS
  unfold Internal.credC Internal.whistC
  rw [Internal.creditScan_append, Internal.creditScan_append, Internal.creditScan_snoc,
    Internal.creditScan_snoc]
  simp only [inside, ↓reduceIte]
  unfold Internal.credC Internal.whistC at first last
  simp only [List.map_append, List.sum_append] at first last ⊢
  exact ⟨by omega, by omega⟩

/-- The key's effective balance when its exit starts on a run, or 0.

It is the amount of the key's departure charge, which reads the effective balance at the exit call.

A key has a charge only if its exit was not assigned at the run's start.

Only a charge whose exit epoch is at most the run's last epoch counts. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.exitQ {x y : ForkedBeaconState preset}
  (tail : Run config checks x y) (v : ℕ) : ℕ :=
  ((tail.departureCharges.find? fun c =>
      c.index == v && decide (c.epoch ≤ (getCurrentEpoch y.state).toNat)).map (·.amount)).getD 0

/-- Whether a run has the key's departure charge, and the epoch rewards of the steps from it on.

The step with the charge counts too, since the key's epoch pass in it follows its exit.

The steps count from the one whose start epoch is at most `high + 1`, as in `Run.balanceEvents`. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.riseScan (v high : ℕ) {x :
  ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → Bool × ℕ
  | _, .nil => (false, 0)
  | _, .snoc (middle := m) pre step =>
    let before := Internal.riseScan v high pre
    (before.1 || step.departureCharges.any (·.index == v),
      if (before.1 = true ∨ step.departureCharges.any (·.index == v) = true) ∧
          (getCurrentEpoch m.state).toNat ≤ high + 1 then
        before.2 + Internal.epochRewards v step
      else before.2)

/-- The key's rise on a run after its exit starts there.

It is one upward band for the rise of the effective balance beyond the key's epoch rewards.

It adds those rewards over the slot steps that come after the step with its departure charge.

It is 0 for a key whose exit does not start on the run. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.riseQ {x y : ForkedBeaconState preset}
  (tail : Run config checks x y)
    (high v : ℕ) : ℕ :=
  if (Internal.riseScan v high tail).1 = true then preset.upwardBand + (Internal.riseScan v high
    tail).2 else 0

/-! ### The keys that a run credits -/

/-- The net credits to a key in the block steps of a run add over `append`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.netScan_append (v high : ℕ) {x m y
  : ForkedBeaconState preset}
    (pre : Run config checks x m) (post : Run config checks m y) :
    Internal.netScan v high (pre.append post) = Internal.netScan v high pre + Internal.netScan v
      high post := by
  induction post with
  | nil => rfl
  | snoc post step ih =>
    change Internal.netScan v high ((pre.append post).snoc step) = _
    rw [Internal.netScan_snoc, Internal.netScan_snoc, ih]
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
  have seatless : ∀ member ∈ (members.zip aggregate.syncCommitteeBits.bits.toArray).toList,
      member.1.toNat ≠ i := signers_elsewhere_of_unseated membersOk found unseated
  obtain ⟨b, held⟩ : ∃ b, c.balances.data[i]? = some b :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  obtain ⟨final, atFinal, value⟩ := balances i b held
  have low := (syncRewards_bounds (reward := reward.toNat)
    (proposerReward := proposerReward.toNat) (index := i) (chosen := chosen) _ b.toNat).2
    (fun member inside _ => seatless member inside)
  rw [← value] at low
  simp only [actualBalanceAt, held, atFinal, Option.map_some, Option.getD_some] at moved ⊢
  by_cases signer : ∃ member ∈ (members.zip aggregate.syncCommitteeBits.bits.toArray).toList,
      member.2 = true ∧ chosen.toNat = i
  · obtain ⟨member, inside, signedBit, same⟩ := signer
    exact ⟨chosen, signed ⟨member, inside, signedBit⟩, same, by omega⟩
  · exfalso
    have high := (syncRewards_bounds (reward := reward.toNat)
      (proposerReward := proposerReward.toNat) (index := i) (chosen := chosen) _ b.toNat).1
      (fun member inside bit => ⟨seatless member inside,
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
      ∀ i, proposer ≠ i → Internal.keyCredit i e = 0)

/-- A carried pass records nothing. -/
private theorem PassCredits.carry {f : Fork} {proposer : ℕ}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    {pre post : BalanceReplay preset f} (held : PassCredits proposer pre.2)
    (ok : carryBalance action pre = .ok post) : PassCredits proposer post.2 := by
  rw [(Internal.carryBalance_cases ok).2]
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
  obtain ⟨_, _, _, computed, events⟩ := recordBalance_single ok
  rw [events]
  intro e member
  rcases List.mem_append.mp member with old | new
  · exact held e old
  · obtain rfl := List.mem_singleton.mp new
    exact ⟨notSync, notConsolidation, fun source i other =>
      Nat.sub_eq_zero_of_le (lowered source post.1 computed i other)⟩

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
      PassCredits block.proposerIndex.toNat rest ∧
      getBeaconProposerIndex a = .ok block.proposerIndex := by
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
    (Internal.carryBalance_cases headedOk).1
  have input : OperationsInput config checks engine a block voted.1 :=
    ⟨a, headed.1, executed.1, revealed.1, by simp [notGloas, pure, Except.pure], headerOk,
      by
        obtain ⟨_, _, _, action, _⟩ := recordBalance_single executedOk
        simpa only [bellatrix, ↓reduceDIte] using action,
      (Internal.carryBalance_cases revealedOk).1,
      by simpa only [before, ↓reduceDIte] using (Internal.carryBalance_cases votedOk).1⟩
  have read := (operationsInput_proposer apart input).1
  -- The operations apply the actions of the replay in order, so they keep that proposer.
  have operated : processOperations config checks voted.1 block.body a.latestBlockHeader.slot =
      .ok consolidated.1 := by
    have pOk := DirectSafety.Apriori.Internal.recordFold_plain _ _ _ _ _ proposedOk
    have sOk := DirectSafety.Apriori.Internal.recordFold_plain _ _ _ _ _ slashedOk
    have aOk := DirectSafety.Apriori.Internal.recordFold_plain _ _ _ _ _ attestedOk
    have dOk := DirectSafety.Apriori.Internal.recordFold_plain _ _ _ _ _ depositedOk
    have cOk := DirectSafety.Apriori.Internal.recordFold_plain _ _ _ _ _ consolidatedOk
    simp only [Array.foldlM_toList] at pOk sOk aOk dOk cOk
    unfold processOperations
    simp only [notGloas, electra, ↓reduceDIte, bind_ok_iff, ensure_ok_iff, processExecutionRequests]
    exact ⟨x1, x2, x3, x4, proposed.1, pOk, slashed.1, sOk, attested.1, aOk, deposited.1, dOk,
      exited.1, (Internal.carryBalance_cases exitedOk).1, changed.1,
      (Internal.carryBalance_cases changedOk).1, requested.1,
      (Internal.carryBalance_cases requestedOk).1, withdrawn.1,
      (Internal.carryBalance_cases withdrawnOk).1, cOk⟩
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
    obtain ⟨_, _, _, actionOk, _⟩ := recordBalance_single ok
    obtain ⟨-, -, kept⟩ := props _ _ actionOk seen
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
  obtain ⟨credit, debit, _, synced, events⟩ := recordBalance_single syncOk
  exact ⟨consolidated.1, consolidated.2, altair, _, credit, debit, events, link, synced,
    consolidatedC, processBlockHeader_proposer headerOk⟩

/-- A key that an event of a block step credits is its proposer, or a seat holder for a sync event.

The mixes must span more than the seed lookahead plus two epochs. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.block_gross_keys {g :
  ForkedBeaconState preset}
    (genesis : Genesis config checks g)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {f : Fork} {s t : BeaconState preset f} {engine : ExecutionEngine preset f}
    {signed : SignedBeaconBlock preset f} {due : upgradeDue config ⟨f, s⟩ = false}
    {ok : applySignedBlock config checks engine s signed true = .ok t}
    (shared : Run config checks g ⟨f, s⟩) (fulu : .fusaka ≤ f) (early : f < .glamsterdam)
    {events : List (BalanceEvent preset)}
    (replayed : (Step.block engine signed due ok).balanceEvents = .ok events) :
    ∃ K : Finset ℕ, K.card ≤ 1 ∧ (∀ k ∈ K, ∃ p, getBeaconProposerIndex s = .ok p ∧ p.toNat = k) ∧
      ∀ e ∈ events, ∀ i, 0 < Internal.keyCredit i e →
      i ∈ K ∨ (e.source = .sync ∧ ∃ altair : .altair ≤ f, ∃ w, t.validators.data[i]? = some w ∧
        w.pubkey ∈ (t.currentSyncCommittee altair).value.pubkeys.toList) := by
  have electra : .pectra ≤ f := Nat.le_trans (by decide) fulu
  obtain ⟨c, rest, altair, aggregate, credit, debit, split, read, synced, passes, header⟩ :=
    blockReplay_proposer_credits apart electra early (Step.balanceEvents_block early replayed)
  have bounded := step_events_bounded shared genesis (Step.block engine signed due ok) early
    replayed
  have matchedT : BalancesMatch t :=
    (frame_processBlock (applySignedBlock_ok ok).2.1).balancesMatch
      (run_justified_separated shared genesis).1.balancesMatch
  refine ⟨{signed.message.proposerIndex.toNat}, by simp,
    fun k hk => ⟨_, header, (Finset.mem_singleton.mp hk).symm⟩, fun e member i positive => ?_⟩
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
      have noSync : Internal.syncCredit i e = 0 := by simp [Internal.syncCredit, notSync]
      have noSlash : ¬ e.source = .slashings := fun h => credited (.inr h)
      simp only [noRewards, noSlash, noSync, ↓reduceIte] at each
      omega
  · obtain rfl := List.mem_singleton.mp inSync
    simp only [Internal.keyCredit] at positive
    rcases sync_moved_seat (i := i) altair synced matchedT (by omega) with h | ⟨_, found, same, -⟩
    · exact .inr ⟨rfl, altair, h⟩
    · exact .inl (Finset.mem_singleton.mpr (by rw [read] at found; cases found; exact same.symm))

/-- A key that rewards, slashings or sync credit in a block step is a proposer or a seat holder. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.block_step_gross_keys {g :
  ForkedBeaconState preset}
    (genesis : Genesis config checks g)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {f : Fork} {s t : BeaconState preset f} {engine : ExecutionEngine preset f}
    {signed : SignedBeaconBlock preset f} {due : upgradeDue config ⟨f, s⟩ = false}
    {ok : applySignedBlock config checks engine s signed true = .ok t}
    (shared : Run config checks g ⟨f, s⟩) (fulu : .fusaka ≤ f) (early : f < .glamsterdam) :
    ∃ K : Finset ℕ, K.card ≤ 1 ∧ (∀ k ∈ K, ∃ p, getBeaconProposerIndex s = .ok p ∧ p.toNat = k) ∧
      ∀ i, 0 < Internal.stepCredit
        (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ => false) i
        (Step.block engine signed due ok) →
      i ∈ K ∨ ∃ altair : .altair ≤ f, ∃ w, t.validators.data[i]? = some w ∧
        w.pubkey ∈ (t.currentSyncCommittee altair).value.pubkeys.toList := by
  cases replayed : (Step.block engine signed due ok).balanceEvents with
  | error _ =>
    exact ⟨∅, by simp, by simp, fun i pos => by simp [Internal.stepCredit, replayed,
      Except.toOption] at pos⟩
  | ok events =>
    obtain ⟨K, card, proposers, keys⟩ := Internal.block_gross_keys genesis apart shared fulu early
      replayed
    refine ⟨K, card, proposers, fun i pos => ?_⟩
    simp only [Internal.stepCredit, replayed, Except.toOption, Option.getD_some] at pos
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

/-- The scan of a run reads the credit of each step that the run contains.

The run must end within the horizon, so that every step of it is selected. -/
private theorem stepCredit_le_creditScan (blockP slotP : BalanceSource → Bool) (v high : ℕ)
    {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
    {a b : ForkedBeaconState preset} (step : Step config checks a b) (member : tail.Contains step) :
    Internal.stepCredit blockP slotP v step ≤ (Internal.creditScan blockP slotP v high tail) := by
  obtain ⟨pre, post, same⟩ := tail.contains_split step member
  subst same
  have selected : (getCurrentEpoch a.state).toNat ≤ high + 1 :=
    Nat.le_trans (UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps
      (Relation.ReflTransGen.head step.chainStep post.chainSteps))) within
  rw [Internal.creditScan_append, Internal.creditScan_snoc]
  simp only [selected, ↓reduceIte]
  omega

/-- A key that a deposit credits on C's run has a positive deposit scan.

A deposit event of a block raises no balance, so a deposit that credits a key is an epoch's.

The scan counts the deposits of a slot step, and the run ends within the horizon. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.depPre_pos_scan (h : Setting config
  checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (i : ℕ) (pos : 0 < Internal.depPre eventsC i) :
    0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i highC tailC) := by
  classical
  obtain ⟨e, member, dep, credited⟩ : ∃ e ∈ eventsC, e.source = .deposits ∧ 0 < Internal.keyCredit i
    e := by
    by_contra none
    have none' : ∀ e ∈ eventsC, e.source = .deposits → Internal.keyCredit i e ≤ 0 := fun e member
      dep =>
      Nat.le_of_not_lt fun positive => none ⟨e, member, dep, positive⟩
    have zero : Internal.depPre eventsC i = 0 := by
      unfold Internal.depPre
      refine List.sum_eq_zero fun x mem => ?_
      obtain ⟨e, filtered, rfl⟩ := List.mem_map.mp mem
      obtain ⟨inEvents, selected⟩ := List.mem_filter.mp filtered
      exact Nat.le_zero.mp (none' e inEvents (of_decide_eq_true selected).1)
    omega
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  rcases (Internal.run_located tailC electra h.early highC replayedC).1 e member dep with
    unconditional | ⟨u, w, ok, es, contains, replayedEs, inEs, -⟩
  · exfalso
    have := unconditional i
    unfold Internal.keyCredit at credited
    omega
  · have step : Internal.keyCredit i e ≤ Internal.stepCredit (fun _ => false) (fun s => decide (s =
    .deposits)) i
        (Step.slot ok : Step config checks u w) := by
      simp only [Internal.stepCredit, replayedEs, Except.toOption, Option.getD_some]
      exact List.le_sum_of_mem (List.mem_map.mpr
        ⟨e, List.mem_filter.mpr ⟨inEs, by simpa using dep⟩, rfl⟩)
    have scan := stepCredit_le_creditScan (fun _ => false) (fun s => decide (s = .deposits)) i highC
      tailC endEpochC (Step.slot ok) contains
    omega

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
      ∀ i, 0 < Internal.stepCredit (fun _ => false) (fun s => decide (s = .deposits)) i step → i ∈ D
        := by
  classical
  cases step with
  | block engine signed due ok =>
    refine ⟨∅, by simp, fun i here => ?_⟩
    exfalso
    have zero : Internal.stepCredit (fun _ => false) (fun s => decide (s = .deposits)) i
        (Step.block engine signed due ok : Step config checks _ _) = 0 := by
      show ((((Step.block (config := config) (checks := checks) engine signed due
        ok).balanceEvents.toOption.getD []).filter ((fun _ => false) ·.source)).map
          (Internal.keyCredit i)).sum = 0
      rw [List.filter_eq_nil_iff.mpr (fun a _ => by simp)]
      rfl
    omega
  | slot across =>
    obtain ⟨events, eventsOk⟩ :=
      (Step.slot across : Step config checks x y).balanceEvents_ok early
    -- A slot step credits a key by deposits only if one of its deposit events does.
    have quiet : ∀ i, (∀ e ∈ events, e.source = .deposits → Internal.keyCredit i e = 0) →
        Internal.stepCredit (fun _ => false) (fun s => decide (s = .deposits)) i
          (Step.slot across : Step config checks x y) = 0 := fun i none' => by
      show (((((Step.slot (config := config) (checks := checks)
        across).balanceEvents.toOption.getD []).filter
          ((fun s => decide (s = .deposits)) ·.source))).map (Internal.keyCredit i)).sum = 0
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
        have mono : ∃ e ∈ events, e.source = .deposits ∧ 0 < Internal.keyCredit i e := by
          by_contra none
          have none' : ∀ e ∈ events, e.source = .deposits → Internal.keyCredit i e = 0 :=
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
        unfold Internal.keyCredit at positive
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
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.credited_piece {g :
  ForkedBeaconState preset}
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
      (∀ i, 0 < Internal.grossScan i high r →
      i ∈ B ∨ ∃ w, y.state.validators.data[i]? = some w ∧
        w.pubkey ∈ (x.state.currentSyncCommittee altair).value.pubkeys.toList) ∧
      (∀ i, 0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i high r) →
        i ∈ D) ∧
      (∀ events, r.balanceEvents high = .ok events → ∀ i, 0 < (events.map (Internal.syncDebit
        i)).sum →
        ∃ w, y.state.validators.data[i]? = some w ∧
          w.pubkey ∈ (x.state.currentSyncCommittee altair).value.pubkeys.toList) ∧
      ∀ i ∈ B, ∃ (u : ForkedBeaconState preset) (_ : Run config checks x u) (p : ValidatorIndex),
        u.fork < .glamsterdam ∧ getBeaconProposerIndex u.state = .ok p ∧ p.toNat = i := by
  classical
  induction r with
  | nil =>
    refine ⟨∅, ∅, by simp, by simp, fun i pos => (Nat.lt_irrefl 0 pos).elim,
      fun i pos => (Nat.lt_irrefl 0 pos).elim, ?_, by simp⟩
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
    obtain ⟨B, D, cardB, cardD, hB, hDep, hS, hP⟩ := ih uEarly uSame
    obtain ⟨Ds, cardDs, hDs⟩ := step_deposit_keys genesis (shared.append pre) step early delay
    have cardUnion : (D ∪ Ds).card ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat *
        ((getCurrentEpoch l.state).toNat - (getCurrentEpoch x.state).toNat) := by
      have joined := Nat.mul_le_mul_left preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat
        (show (getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat +
          ((getCurrentEpoch l.state).toNat - (getCurrentEpoch u.state).toNat) ≤
            (getCurrentEpoch l.state).toNat - (getCurrentEpoch x.state).toNat by omega)
      rw [Nat.mul_add] at joined
      exact (Finset.card_union_le _ _).trans (Nat.le_trans (Nat.add_le_add cardD cardDs) joined)
    have depMem : ∀ i, 0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i
      high
        (pre.snoc step)) → i ∈ D ∪ Ds := by
      intro i pos
      rw [Internal.creditScan_snoc] at pos
      split at pos
      · by_cases prior : 0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits))
        i
            high pre)
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
      refine ⟨B, D ∪ Ds, cardB, cardUnion, fun i pos => ?_, depMem, ?_, hP⟩
      have prior := grossScan_slot_pos i high pre ok pos
      rcases hB i prior with member | ⟨w, found, mem⟩
      · exact .inl member
      · exact .inr (carry i w found mem)
      intro events replayed i pos
      simp only [Run.balanceEvents, bind_ok_iff] at replayed
      obtain ⟨prior, priorOk, rest⟩ := replayed
      split at rest
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
        obtain ⟨added, addedOk, rfl⟩ := rest
        have zero := (Internal.slot_syncDebit_zero
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
      obtain ⟨K, cardK, hKp, hK⟩ := Internal.block_step_gross_keys (engine := engine) (signed :=
        signed)
        (due := due) (ok := ok) genesis apart (shared.append pre) fulu' uEarly
      refine ⟨B ∪ K, D ∪ Ds, ?_, cardUnion, fun i pos => ?_, depMem, ?_, fun i hi => ?_⟩
      · exact (Finset.card_union_le _ _).trans (Nat.add_le_add cardB cardK)
      · rw [Internal.grossScan_snoc] at pos
        rcases Nat.eq_zero_or_pos (Internal.grossScan i high pre) with zero | prior
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
          by_cases first : 0 < (prior.map (Internal.syncDebit i)).sum
          · obtain ⟨w, found, mem⟩ := hS prior priorOk i first
            exact carry i w found mem
          · have here : 0 < (added.map (Internal.syncDebit i)).sum := by omega
            have altair' : .altair ≤ f := Nat.le_trans (by decide) fulu'
            obtain ⟨c, rest', aggregate, credit, debit, rfl, silent, -, synced⟩ :=
              PinSeatDebits.blockReplay_sync_split (show f < .glamsterdam from uEarly) altair'
                (Step.balanceEvents_block uEarly addedOk)
            simp only [List.map_append, List.sum_append, silent, Internal.syncDebit, ↓reduceIte,
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
      · -- a proposer of an earlier block, or the proposer of this one
        rcases Finset.mem_union.mp hi with earlier | here
        · exact hP i earlier
        · obtain ⟨p, found, same⟩ := hKp i here
          exact ⟨⟨f, s⟩, pre, p, uEarly, found, same⟩

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

/-- The keys credited in the block steps of a run, counted by the periods that it touches.

The keys that a sync aggregate debits hold a seat of one committee for each period of the run.

Each committee is the current one at a state of the run, in the period of its index. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.credited_pieces_seated {g :
  ForkedBeaconState preset}
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
      (∀ i, 0 < Internal.grossScan i high r → i ∈ B ∨ i ∈ S) ∧
      (∀ i, 0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i high r) →
        i ∈ D) ∧
      (∀ i, 0 < Internal.grossScan i high r → i ∈ B ∨
        ∃ w j, y.state.validators.data[i]? = some w ∧ j ≤ n ∧ w.pubkey ∈ Ls j) ∧
      (∀ i ∈ B, ∃ (u : ForkedBeaconState preset) (_ : Run config checks x u) (p : ValidatorIndex),
        u.fork < .glamsterdam ∧ getBeaconProposerIndex u.state = .ok p ∧ p.toNat = i) ∧
      (∀ events, r.balanceEvents high = .ok events → ∀ i, 0 < (events.map (Internal.syncDebit
        i)).sum →
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
    obtain ⟨B, D, cardB, cardD, hB, hDep, hD, hP⟩ := Internal.credited_piece genesis apart shared r
      fulu
      altair early delay high (by simpa using count)
    obtain ⟨S, cardS, hS⟩ := seat_positions genesis shared r altair
    refine ⟨fun _ => (x.state.currentSyncCommittee altair).value.pubkeys.toList, B, S, D, cardB,
      by simpa using cardS, cardD, fun i pos => ?_, hDep,
      fun i pos => (hB i pos).imp id fun ⟨w, found, mem⟩ => ⟨w, 0, found, Nat.le_refl _, mem⟩, hP,
      ?_, ?_⟩
    · rcases hB i pos with member | ⟨w, found, mem⟩
      · exact .inl member
      · exact .inr (hS i w found mem)
    · intro events replayed i pos
      obtain ⟨w, found, mem⟩ := hD events replayed i pos
      exact ⟨hS i w found mem, w, 0, found, Nat.le_refl _, mem⟩
    · intro j hj
      obtain rfl : j = 0 := by omega
      exact ⟨x, Run.nil, r, altair, Run.nil_append r, (Nat.add_zero _).symm, rfl⟩
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
    have up := step.chainStep.epoch_le_succ
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
      rw [Nat.succ_div] at above
      split at above <;> omega
    have mEarly : m.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (Nat.le_trans step.chainStep.fork_le
        (fork_le_of_chainSteps post.chainSteps)) early
    have vFulu : .fusaka ≤ v.fork :=
      Nat.le_trans fulu (fork_le_of_chainSteps (pre.snoc step).chainSteps)
    obtain ⟨B₁, D₁, cardB₁, cardD₁, hB₁, hDep₁, hD₁, hP₁⟩ := Internal.credited_piece genesis apart
      shared pre
      fulu
      altair mEarly delay high (by simpa using mSame)
    obtain ⟨S₁, cardS₁, hS₁⟩ := seat_positions genesis shared pre altair
    obtain ⟨Ls₂, B₂, S₂, D₂, cardB₂, cardS₂, cardD₂, hB₂, hDep₂, hG₂, hP₂, hD₂, hz₂⟩ := ih (x := v)
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
      fun i pos => ?_, fun i pos => ?_, fun i hi => ?_, ?_, ?_⟩
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
    · rw [Internal.grossScan_append] at pos
      by_cases first : 0 < Internal.grossScan i high (pre.snoc (Step.slot ok))
      · have prior := grossScan_slot_pos i high pre ok first
        rcases hB₁ i prior with member | ⟨w, found, mem⟩
        · exact .inl (Finset.mem_union_left _ member)
        · exact .inr (Finset.mem_union_left _ (hS₁ i w found mem))
      · have later : 0 < Internal.grossScan i high post := by omega
        rcases hB₂ i later with member | member
        · exact .inl (Finset.mem_union_right _ member)
        · exact .inr (Finset.mem_union_right _ member)
    · rw [Internal.creditScan_append] at pos
      by_cases first : 0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i
        high
          (pre.snoc (Step.slot ok)))
      · rw [Internal.creditScan_snoc] at first
        split at first
        · by_cases prior : 0 < (Internal.creditScan (fun _ => false)
              (fun s => decide (s = .deposits)) i high pre)
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hDep₁ i prior))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hDs i (by omega)))
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hDep₁ i first))
      · exact Finset.mem_union_right _ (hDep₂ i (by omega))
    · -- a credit in the first part is a proposer or a seat holder, and a seat persists
      rw [Internal.grossScan_append] at pos
      by_cases first : 0 < Internal.grossScan i high (pre.snoc (Step.slot ok))
      · have prior := grossScan_slot_pos i high pre ok first
        rcases hB₁ i prior with member | ⟨w, found, mem⟩
        · exact .inl (Finset.mem_union_left _ member)
        · have kept := (validatorKeys_prefix_and_distinct_of_chainSteps
            (Relation.ReflTransGen.head (Step.slot ok : Step config checks m v).chainStep
              post.chainSteps)).1
          obtain ⟨w', found', same⟩ := validators_getElem?_of_validatorKeys_prefix kept found
          exact .inr ⟨w', 0, found', Nat.zero_le _, by simpa [same] using mem⟩
      · rcases hG₂ i (by omega) with member | ⟨w, j, found, hj, mem⟩
        · exact .inl (Finset.mem_union_right _ member)
        · exact .inr ⟨w, j + 1, found, by omega, by simpa using mem⟩
    · rcases Finset.mem_union.mp hi with first | later
      · exact hP₁ i first
      · obtain ⟨u, q, p, early', found, same⟩ := hP₂ i later
        exact ⟨u, (pre.snoc (Step.slot ok)).append q, p, early', found, same⟩
    · intro events replayed i pos
      obtain ⟨e1, ok1⟩ := (pre.snoc (Step.slot ok)).balanceEvents_ok vEarly high
      obtain ⟨e2, ok2⟩ := post.balanceEvents_ok early high
      rw [DirectSafety.Apriori.Internal.balanceEvents_append _ _ high ok1 ok2] at replayed
      have joined := Except.ok.inj replayed
      subst joined
      simp only [List.map_append, List.sum_append] at pos
      by_cases first : 0 < ((e1.map (Internal.syncDebit i))).sum
      · have seated : ∃ w, m.state.validators.data[i]? = some w ∧
            w.pubkey ∈ (x.state.currentSyncCommittee altair).value.pubkeys.toList := by
          simp only [Run.balanceEvents, bind_ok_iff] at ok1
          obtain ⟨prior, priorOk, rest⟩ := ok1
          split at rest
          · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
            obtain ⟨added, addedOk, rfl⟩ := rest
            have zero := (Internal.slot_syncDebit_zero
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
        exact ⟨x, Run.nil, (pre.snoc (Step.slot ok)).append post, altair, Run.nil_append _,
          (Nat.add_zero _).symm, by simp⟩
      · obtain ⟨z, r1, r2, alt, cut, per, hL⟩ := hz₂ (j - 1) (by omega)
        refine ⟨z, (pre.snoc (Step.slot ok)).append r1, r2, alt, ?_, ?_, ?_⟩
        · rw [← Run.append_assoc, cut]
        · omega
        · simpa [j0] using hL

/-- The keys credited in the block steps of a run, counted by the periods that it touches. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.credited_pieces {g :
  ForkedBeaconState preset}
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
      (∀ i, 0 < Internal.grossScan i high r → i ∈ B ∨ i ∈ S) ∧
      (∀ i, 0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i high r) →
        i ∈ D) ∧
      ∀ events, r.balanceEvents high = .ok events → ∀ i, 0 < (events.map (Internal.syncDebit i)).sum
        →
        i ∈ S := by
  intro n x shared r fulu count
  obtain ⟨_, B, S, D, cardB, cardS, cardD, hBS, hDep, -, -, hSD, _⟩ :=
    Internal.credited_pieces_seated genesis apart early delay high n shared r fulu count
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
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.seat_union_card (h : Setting config
  checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (high highC : ℕ)
    {events eventsF eventsC : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (replayedF : fromFin.balanceEvents highC = .ok eventsF)
    (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (altairF : .altair ≤ fork) (AV AK : Finset ℕ)
    (debitsC : ∀ i ∈ AV, 0 < ((eventsF ++ eventsC).map (Internal.syncDebit i)).sum ∨
      (0 < Internal.grossScan i highC (fromFin.append tailC) ∧
        ∀ (u : ForkedBeaconState preset) (_ : Run config checks ⟨fork, fin⟩ u) (p : ValidatorIndex),
          u.fork < .glamsterdam → getBeaconProposerIndex u.state = .ok p → p.toNat ≠ i) ∨
      ∃ w, split.validators.data[i]? = some w ∧
        w.pubkey ∈ (split.currentSyncCommittee altairF).value.pubkeys.toList)
    (debitsR : ∀ i ∈ AK, 0 < (events.map (Internal.syncDebit i)).sum) :
    (AV ∪ AK).card ≤ preset.SYNC_COMMITTEE_SIZE.toNat *
      (((getCurrentEpoch pulled).toNat + 1) /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
        (getCurrentEpoch fin).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 1 +
      ((getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat) /
        max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) := by
  classical
  obtain ⟨toFin⟩ := h.toFin
  have apart := h.parameters.lookahead
  have finSplit := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have splitPulled := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
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
  obtain ⟨LsR, BR, SR, DR, -, -, -, -, -, -, -, debitR, familyR⟩ :=
    Internal.credited_pieces_seated h.genesis apart (y := ⟨fork, pulled⟩) h.early
      (Internal.Setting.delay h) high
      ((getCurrentEpoch pulled).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
        (getCurrentEpoch split).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
      (toFin.append fromFin) tail h.fulu (by rw [hP]; exact periodsR)
  obtain ⟨LsC, BC, SC, DC, -, -, -, -, -, grossC, propC, debitC, familyC⟩ :=
    Internal.credited_pieces_seated h.genesis apart (y := ⟨fork, counted⟩) h.early
      (Internal.Setting.delay h) highC
      ((getCurrentEpoch counted).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
        (getCurrentEpoch fin).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
      toFin (fromFin.append tailC) h.fulu (by rw [hP]; exact periodsC)
  simp only [hP] at familyR familyC debitR debitC grossC
  have replayedRC : (fromFin.append tailC).balanceEvents highC = .ok (eventsF ++ eventsC) :=
    DirectSafety.Apriori.Internal.balanceEvents_append fromFin tailC highC replayedF replayedC
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
      h.facts.syncPeriod (by rw [hP]; simpa using per) alt altairF
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
        h.facts.syncPeriod (by rw [hP]; simp only; omega) alt altairF
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
    · -- a key debited or credited on C's run holds a seat, unless it is a proposer
      obtain ⟨w, j, found, hj, mem⟩ : ∃ (w : Validator) (j : ℕ),
          counted.validators.data[i]? = some w ∧ j ≤ nC ∧ w.pubkey ∈ LsC j := by
        rcases debitsC i inV with spent | ⟨seen, notProposer⟩ | ⟨ws, foundS, memS⟩
        · obtain ⟨-, w, j, found, hj, mem⟩ := debitC (eventsF ++ eventsC) replayedRC i spent
          exact ⟨w, j, found, hj, mem⟩
        · rcases grossC i seen with proposed | ⟨w, j, found, hj, mem⟩
          · obtain ⟨u, q, p, early', found, same⟩ := propC i proposed
            exact absurd same (notProposer u q p early' found)
          · exact ⟨w, j, found, hj, mem⟩
        · -- a seat of the split's current committee, which C's committees hold
          obtain ⟨jc, hjc, e⟩ := firstC
          obtain ⟨c, foundC, sameC⟩ := validators_getElem?_of_validatorKeys_prefix keptC foundS
          exact ⟨c, jc, foundC, hjc, by rw [sameC, e]; exact memS⟩
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
    (keys : Finset ℕ) (banded : ∀ i ∈ keys, 0 < Internal.grossScan i high tail +
      (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i high tail) +
        (events.map (Internal.syncDebit i)).sum) :
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
  obtain ⟨B, S, D, cardB, cardS, cardD, hBS, hD, hSD⟩ := Internal.credited_pieces h.genesis apart
    (y := ⟨fork, x⟩) h.early (Internal.Setting.delay h) high
    ((getCurrentEpoch x).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
      (getCurrentEpoch split).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
    shared tail h.fulu periods
  have cardD' : D.card ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat *
      ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat) := cardD
  have subset : keys ⊆ B ∪ S ∪ D := fun i member => by
    have pos := banded i member
    by_cases net : 0 < Internal.grossScan i high tail
    · rcases hBS i net with inB | inS
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ inB)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ inS)
    · by_cases dep : 0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i
      high
          tail)
      · exact Finset.mem_union_right _ (hD i dep)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hSD events replayed i (by omega)))
  -- The blocks of the run are at most one for each slot of its epochs.
  have blocks : tail.blockCount ≤
      ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat + 1) *
        preset.SLOTS_PER_EPOCH.toNat := by
    have count : tail.blockCount ≤
        ((getCurrentEpoch x).toNat + 1 - (getCurrentEpoch split).toNat) *
          preset.SLOTS_PER_EPOCH.toNat := tail.blockCount_le_epochs positive
    have same : (getCurrentEpoch x).toNat + 1 - (getCurrentEpoch split).toNat =
        (getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat + 1 := by omega
    rw [same] at count
    exact count
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
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.credited_keys_le (h : Setting
  config checks g split fin pulled anc counted V)
    {x : BeaconState preset fork} (tail : Run config checks ⟨fork, split⟩ ⟨fork, x⟩) (high : ℕ) :
    ((Finset.range x.validators.data.size).filter fun i =>
        0 < Internal.grossScan i high tail +
          (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i high tail)).card
            ≤
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

/-- The keys active at C. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.AC := activeVoters counted

/-- The keys active at R. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.AR := activeVoters pulled

/-- The keys counted in C's quorum. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Q := quorumVoters counted

/-- The keys that the costs sum over: counted at C, or active at C or R. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.U := Internal.Q counted ∪ Internal.AC
  counted ∪ Internal.AR pulled

/-- The balance of a key at C. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.eC (v : ValidatorIndex) : ℕ :=
  balanceAt counted v.toNat

/-- The balance of a key at R. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.eR (v : ValidatorIndex) : ℕ :=
  balanceAt pulled v.toNat

/-- V keys active in C: twice their fall. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.cV1 : ℤ := ∑ v ∈ Internal.U pulled
  counted,
  if v ∈ V ∧ v ∈ Internal.AC counted then (Internal.eR pulled v : ℤ) - Internal.eC counted v else 0

/-- V keys not active in C: twice their stake at R. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.cV2 : ℤ :=
  ∑ v ∈ Internal.U pulled counted, if v ∈ V ∧ v ∉ Internal.AC counted then (Internal.eR pulled v :
    ℤ) else 0

/-- (K4 pulled counted V), other keys active in both and counted in C: once their rise. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.cN : ℤ := ∑ v ∈ Internal.U pulled
  counted,
  if v ∈ Internal.AC counted ∧ v ∈ Internal.AR pulled ∧ v ∈ Internal.Q counted ∧ v ∉ V then
    (Internal.eC counted v : ℤ) - Internal.eR pulled v else 0

/-- (K5 counted V), other keys previous-epoch-only in C: three times their stake at C. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.cP : ℤ := ∑ v ∈ Internal.U pulled
  counted,
  if v ∈ Internal.Q counted ∧ v ∉ Internal.AC counted ∧ v ∉ V then (Internal.eC counted v : ℤ) else
    0

/-- (K6 pulled counted), keys counted in C and not active at R: once their stake at C. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.cJ : ℤ := ∑ v ∈ Internal.U pulled
  counted,
  if v ∈ Internal.AC counted ∧ v ∈ Internal.Q counted ∧ v ∉ Internal.AR pulled then (Internal.eC
    counted v : ℤ) else 0

/-- The keys active at C and outside its quorum (slashed at C): minus twice their stake at C.

It also subtracts their stake at R if they are active there. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.cK7 : ℤ := ∑ v ∈ Internal.U pulled
  counted,
  if v ∈ Internal.AC counted ∧ v ∉ Internal.Q counted then
    -(2 * (Internal.eC counted v : ℤ)) - (if v ∈ Internal.AR pulled then (Internal.eR pulled v : ℤ)
      else 0) else 0

/-- cS, other keys active at R, not at C and outside C's quorum: minus their stake at R. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.cS : ℤ := ∑ v ∈ Internal.U pulled
  counted,
  if v ∈ Internal.AR pulled ∧ v ∉ Internal.AC counted ∧ v ∉ Internal.Q counted ∧ v ∉ V then
    -(Internal.eR pulled v : ℤ) else 0

/-- The keys of `V` not active at C. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.VN : Finset ValidatorIndex := V.filter
  (· ∉ Internal.AC counted)

/-- The keys outside `V` active at C and R and counted in C's quorum. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.K4 : Finset ValidatorIndex :=
  (Internal.AC counted).filter fun v => v ∈ Internal.AR pulled ∧ v ∈ Internal.Q counted ∧ v ∉ V

/-- The keys outside `V` counted in C's quorum but not active at C. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.K5 : Finset ValidatorIndex :=
  (Internal.Q counted).filter fun v => v ∉ Internal.AC counted ∧ v ∉ V

/-- The keys active and counted at C but not active at R. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.K6 : Finset ValidatorIndex :=
  (Internal.AC counted).filter fun v => v ∈ Internal.Q counted ∧ v ∉ Internal.AR pulled

/-- SC, keys of R's registry unslashed at the split and slashed at C. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.SC (split : BeaconState preset fork) :
  Finset ValidatorIndex :=
  ((Finset.range pulled.validators.data.size).image UInt64.ofNat).filter fun v =>
    slashedFlagAt counted v.toNat = some true ∧ slashedFlagAt split v.toNat = some false

/-- Keys created beyond the split's registry and slashed at C. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.CS (split : BeaconState preset fork) :
  Finset ValidatorIndex :=
  ((Finset.range counted.validators.data.size).image UInt64.ofNat).filter fun v =>
    split.validators.data.size ≤ v.toNat ∧ slashedFlagAt counted v.toNat = some true

end Costs

/-! ## Sums over validator indices, read at positions -/

/-- A position that holds a validator and meets a test is among the positions that meet it. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.mem_positions_filter (config :
  Config)
    (state ancestor finalizedState : BeaconState preset fork) {i : ℕ} {w : Validator}
    (found : state.validators.data[i]? = some w) {p : ℕ → Prop} [DecidablePred p] (test : p i) :
    i ∈ (pinTerms config state ancestor finalizedState).positions.filter p :=
  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1, test⟩

/-- A flag read from the validator at a position can hold only where the position holds one.

The flag is the `any` of the validator, or its `map` read with a default of `false`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.validator_of_flag {state :
  BeaconState preset fork} {i : ℕ} {f : Validator → Bool}
    (flag : (state.validators.data[i]?).any f = true ∨
      ((state.validators.data[i]?).map f).getD false = true) :
    ∃ w, state.validators.data[i]? = some w := by
  cases found : state.validators.data[i]? with
  | none =>
    rw [found] at flag
    simp at flag
  | some w => exact ⟨w, rfl⟩

/-- A voter active at the epoch of a state holds a validator there that is active at that epoch. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.active_of_activeVoters (early :
  fork < .glamsterdam)
    {s : BeaconState preset fork} {v : ValidatorIndex} (member : v ∈ activeVoters s) :
    ∃ w, s.validators.data[v.toNat]? = some w ∧
      isActiveValidator w (getCurrentEpoch s) = true := by
  have listed : v ∈ getActiveValidatorIndices s (getCurrentEpoch s) := by
    simpa [activeVoters] using member
  exact (mem_getActiveValidatorIndices (s.validators.bound early)).mp listed

end PinDrift
end EthLib.Consensus.Models.Network
