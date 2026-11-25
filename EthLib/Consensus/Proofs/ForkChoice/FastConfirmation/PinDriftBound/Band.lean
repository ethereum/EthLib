module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumReserve
public import EthLib.Consensus.Proofs.Transition.EpochReads
import EthLib.Consensus.Proofs.Transition.InactivityLeakBound
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumDriftBound
import EthLib.Consensus.Proofs.Transition.SlashedFlags
import EthLib.Consensus.Proofs.Transition.LookaheadActive
import EthLib.Consensus.Proofs.DirectSafety.Apriori.BlockFold
public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Ownership
import Mathlib.Algebra.Order.Floor.Div

/-!
# The quorum of a call drifts by at most its pin reserve, on another branch

A call of the fast confirmation rule reads the pulled-up head state R of an honest store.

A counting state C of another honest store may lie on another branch since the finalized checkpoint.

The two branches leave one split state, at or after the finalized checkpoint's epoch.

The pin reserve bounds quorum drift from R to C for `fusaka ≤ fork < glamsterdam`.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-! ## Keys active only in the previous epoch of the counting state

A key that counts in C's quorum but is not active at C's epoch exits by the epoch after R's.

When activity up to C's epoch is fixed at the split, R reads that exit exactly.

So the pin reserve charges the stake of these scheduled exits. -/

namespace PinDrift.Internal

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

/-- A validator that first appears in a step, at a position the first state lacks, is unslashed. -/
theorem fresh_unslashed {g m n : ForkedBeaconState preset}
    (toM : Run config checks g m) (step : Step config checks m n)
    (genesis : Genesis config checks g) {i : ℕ} (fresh : m.state.validators.data.size ≤ i)
    {w : Validator} (found : n.state.validators.data[i]? = some w) : w.slashed = false := by
  by_contra not
  have slashed : w.slashed = true := by simpa using not
  -- The keys of a run from genesis are distinct.
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
  -- A slashed validator of the last state has a slashed key at the first state.
  --
  -- Otherwise the step carries a slashing that names its key.
  --
  -- Either way a validator of the first state holds that key.
  rcases (Run.nil.snoc step).slashed_evidence w member slashed with
    ⟨v, memberV, key, -⟩ | ⟨a, b, st, contained, evidence⟩
  · obtain ⟨j, read⟩ := List.mem_iff_getElem?.mp memberV
    exact taken j v (by simpa using read) key
  · cases contained with
    | last =>
      obtain ⟨j, v, read, key⟩ := slashingEvidence_key step evidence
      exact taken j v read key
    | earlier inner _ => cases inner

/-- A key that R slashed and C did not has waited the slashings vector. -/
theorem slashed_waits {g : ForkedBeaconState preset}
    {split pulled counted : BeaconState preset fork}
    (toSplit : Run config checks g ⟨fork, split⟩) (genesis : Genesis config checks g)
    (toPulled : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    (toCounted : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    (caps : CapOrder preset)
    (withdrawDelay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {i : ℕ} {validator : Validator} (found : pulled.validators.data[i]? = some validator)
    -- The key is slashed on R's branch after the split, or after it joined.
    (slashed : validator.slashed = true)
    -- Such a key was slashed after the split, since C does not hold the slashing.
    (unslashedC : ((counted.validators.data[i]?).map (·.slashed)).getD true = false) :
    -- A slashing sets the withdrawable epoch at least `EPOCHS_PER_SLASHINGS_VECTOR` after it.
    --
    -- So the withdrawable epoch is at least the split's epoch plus `EPOCHS_PER_SLASHINGS_VECTOR`.
    (getCurrentEpoch split).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
      validator.withdrawableEpoch.toNat := by
  -- The key may be one of the split's registry, or one that joined the registry after the split.
  by_cases inside : i < split.validators.data.size
  · have oldFound := Array.getElem?_eq_getElem inside
    cases oldSlashed : split.validators.data[i].slashed
    · exact (toPulled.newly_slashed_withdrawableEpoch caps
        withdrawDelay i _ validator oldFound found oldSlashed slashed).2
    -- A run keeps every slashing.
    --
    -- So the counting state would hold a key slashed at the split slashed.
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
    have delayed := (post.newly_slashed_withdrawableEpoch caps
      withdrawDelay i w validator arrivedFound found unslashedAtN slashed).2
    have forward : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch n.state).toNat :=
      UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps (pre.snoc step).chainSteps)
    omega

end PinDrift.Internal

open DirectSafety DirectSafety.Apriori.Internal

/-! ## The penalties of one key over several epochs

A key pays penalties only in the rewards pass at the end of each epoch.

So a bound on the pass rate at each last state of an epoch bounds its penalties over the branch. -/

namespace PinDrift.Internal

/-- The rate at which one rewards pass can debit a key, read at the last state of the epoch.

It reads the total active balance, the key's effective balance and its score there.

The pass reads the score after its update, which adds at most the score bias. -/
def passPenaltyRate (config : Config) (z : ForkedBeaconState preset) (v : ℕ) : ℕ :=
  let total := activeBalanceTotal z.state
  let score := if altair : .altair ≤ z.fork then
      (((z.state.inactivityScores altair).data[v]?).map (·.toNat)).getD 0 else 0
  (TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat) * preset.BASE_REWARD_FACTOR.toNat *
      effectiveAt z v / (WEIGHT_DENOMINATOR.toNat * total.sqrt) +
    effectiveAt z v * (score + config.INACTIVITY_SCORE_BIAS.toNat) /
      (config.INACTIVITY_SCORE_BIAS.toNat *
        (parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat)

/-- The penalties of one key in one segment of a branch fit its pass rate.

This holds if the segment ends an epoch, and the penalties are zero otherwise. -/
theorem segment_passDebit_le_guarded {m n : ForkedBeaconState preset}
    (mid : Run config checks m n) (early : n.fork < .glamsterdam) (altair : .altair ≤ m.fork)
    (high : ℕ) (endEpoch : (getCurrentEpoch n.state).toNat ≤ high + 1)
    -- Every step of the segment starts at the epoch of its start `m`.
    (starts : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      mid.Contains step → getCurrentEpoch u.state = getCurrentEpoch m.state)
    {v : ℕ} (inside : v < m.state.validators.data.size) (pen : ℕ)
    -- The rate is asked only at the last pass state.
    --
    -- It is asked only when that state reads a total active balance.
    --
    -- That state must also read a base reward per increment.
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
    --
    -- So a segment that stays in its epoch pays nothing.
    have free := (epoch_sync_data mid altair early same high replayed).2.1
    rw [penaltyDebit_sum_zero_of_free free]
    exact Nat.zero_le _
  -- The slot that ends the epoch runs the rewards pass, read at its last state.
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

Summing the bounds for the segments covers the entire run. -/
theorem Run.passDebit_le {x y : ForkedBeaconState preset} (tail : Run config checks x y)
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
def syncDebit (v : ℕ) (event : BalanceEvent preset) : ℕ :=
  if event.source = .sync then actualBalanceAt event.before v - actualBalanceAt event.after v else 0

/-- The sync credit of a key in one event. -/
def syncCredit (v : ℕ) (event : BalanceEvent preset) : ℕ :=
  if event.source = .sync then actualBalanceAt event.after v - actualBalanceAt event.before v else 0

/-- The balance of a key that stays unslashed falls over a branch only by its debits, as events. -/
theorem Run.balanceFloor_events_or_fulu {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (early : y.fork < .glamsterdam) (high : ℕ)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (v : ValidatorIndex) (val : Validator) (initial : x.state.validators.data[v.toNat]? = some val)
    (unslashed : val.slashed = false)
    -- A key with no activation epoch is allowed if the branch starts from Fulu or later.
    (activated : val.activationEpoch ≠ FAR_FUTURE_EPOCH ∨ .fusaka ≤ x.fork)
    (quotient : ℕ) (positive : 0 < quotient)
    -- The guards are those of the per-key floor of the a priori bound.
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
    -- The balance starts from the smaller of its value and the largest effective balance.
    min (actualBalanceAt x v.toNat) (withdrawalMaxEffectiveBalance preset x.fork val).toNat ≤
      -- The debits are the penalties, the sync penalties and the partial withdrawals of its events.
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

The entries counted are those due by the cutoff. -/
theorem Run.partialDebit_net {x y : ForkedBeaconState preset}
    -- The branch is from Electra.
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (high cutoff : ℕ) (endpoint : (getCurrentEpoch y.state).toNat ≤ cutoff)
    -- The cutoff is less than the start epoch plus the minimum withdrawability delay.
    --
    -- This leaves out the extra wait before exit churn can start.
    --
    -- That wait is one epoch plus the seed lookahead.
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
theorem Run.partialDebit_le {x y : ForkedBeaconState preset}
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

end PinDrift.Internal

/-! ## The band of totals from the guard at the finalized state

The reserve bounds the rates on both branches using the call's total active balance.

The a priori guard at the finalized state supplies a floor and a ceiling on each total. -/

section Band

open DirectSafety.Apriori

namespace PinDrift.Internal

/-- From Electra, the ceiling of a window grows with the epoch of the window. -/
theorem stakeCeilingAt_mono {x : ForkedBeaconState preset} {high : ℕ}
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
theorem stakeFloorAt_anti {x : ForkedBeaconState preset} {high : ℕ} {s t : ℕ}
    (le : s ≤ t) : stakeFloorAt config x high t ≤ stakeFloorAt config x high s := by
  induction le with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    refine Nat.le_trans ?_ ih
    simp only [stakeFloorAt, stakeFloor, stakeFloorPath]
    omega

/-- From Electra, the guard bounds twice the window's last ceiling by three times its last floor.

The window's last index is the epoch after `high`, counted from the guarded state's epoch. -/
theorem ratio_of_guard {x : ForkedBeaconState preset} {high : ℕ}
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
theorem total_within_guard {g x z : ForkedBeaconState preset} {high : ℕ}
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

So the band follows from the guard, and nothing assumes it. -/
theorem total_band_of_guard {g x y z : ForkedBeaconState preset} {high : ℕ}
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
  -- The guard asks that twice the last ceiling be at most three times the last floor.
  have ratio := PinDrift.Internal.ratio_of_guard electra guard
  -- Both totals lie between the window's last floor and ceiling.
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

end PinDrift.Internal

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

namespace PinDrift.Internal

/-- The downward band is below an increment.

Four bands fit in an increment, and an increment is positive. -/
theorem PinPresetFacts.below (facts : PinPresetFacts preset) :
    preset.downwardBand < preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  have := facts.quarterBand
  have := facts.incrementSize
  omega

/-- The base reward factor is positive, since its product with an increment is at least `2 ^ 35`. -/
theorem PinPresetFacts.reward (facts : PinPresetFacts preset) :
    1 ≤ preset.BASE_REWARD_FACTOR.toNat := by
  have scale := facts.rewardScale
  rcases Nat.eq_zero_or_pos preset.BASE_REWARD_FACTOR.toNat with zero | positive
  · rw [zero, Nat.mul_zero] at scale
    exact absurd scale (by decide)
  · exact positive

/-- Forty-four slashings vectors fit in three increments.

It compares epochs with gwei, since the unit gain adds two gwei of rounding for each epoch.

An increment is at least 900 slashings vectors. -/
theorem PinPresetFacts.vectorSmall (facts : PinPresetFacts preset) :
    44 * preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  have := facts.rounding
  omega

end PinDrift.Internal

/-- The mainnet preset has the preset facts of the pin. -/
theorem PinPresetFacts.mainnet : PinPresetFacts Preset.mainnet :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    fun fork => by cases fork <;> decide, fun fork => by cases fork <;> decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide,
    ActivationWithinMaxEffective.mainnet⟩

/-- The minimal preset has the preset facts of the pin.

On minimal, half the slashings vector is 32 epochs.

So the pin's guard holds only at a call at most 27 epochs past the finalized state. -/
theorem PinPresetFacts.minimal : PinPresetFacts Preset.minimal :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    fun fork => by cases fork <;> decide, fun fork => by cases fork <;> decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide,
    ActivationWithinMaxEffective.minimal⟩

namespace PinDrift.Internal

/-- From Electra and before Gloas, the floor of the window at its start leaves room for the window.

The first floor is at least two thirds of an increment. -/
theorem first_floor_of_guard {g x : ForkedBeaconState preset} {high : ℕ}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (aligned : MaxEffectiveBalancesAligned preset)
    (xEarly : x.fork < .glamsterdam)
    (electra : .pectra ≤ x.fork) (guard : aprioriGuardAt config x high)
    (facts : PinPresetFacts preset) :
    -- The window is shorter than the slashings vector, and an increment is at least 900 vectors.
    600 * (high + 2 - (getCurrentEpoch x.state).toNat) ≤ stakeFloorAt config x high 0 ∧
      -- An increment is also at least 14 slashing quotients.
      --
      -- So the first floor is at least 9 quotients.
      9 * (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat ≤
        stakeFloorAt config x high 0 := by
  have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
  have zero : preElectraEpochs config x high = 0 := by simp [preElectraEpochs, notBefore]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, window, -⟩ := id guard
  -- The guard asks that twice the last ceiling be at most three times the last floor.
  have ratio := PinDrift.Internal.ratio_of_guard electra guard
  -- The ceiling is at least an increment, and the floor falls with the epoch of the window.
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

end PinDrift.Internal

end Band

namespace PinDrift.Internal

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

The deposit queue postpones deposits to such a key. -/
theorem processPendingDeposits_exited_balance {state after : BeaconState preset fork}
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

end PinDrift.Internal

end EthLib.Consensus.Models.Network
