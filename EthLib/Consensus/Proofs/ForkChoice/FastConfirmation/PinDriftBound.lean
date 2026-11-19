module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumReserve
public import EthLib.Consensus.Proofs.Transition.BalanceDrift
public import EthLib.Consensus.Proofs.Transition.FfgJustification
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.SlashedExit
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
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Assembly
import EthLib.Consensus.Proofs.Transition.BalanceNotRaised
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
import EthLib.Consensus.Proofs.Transition.ValidatorCaps
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Bound
import EthLib.Consensus.Proofs.Transition.Totality.Supply
import EthLib.Consensus.Proofs.Transition.EffectiveFall
import EthLib.Consensus.Proofs.DirectSafety.Evidence
import EthLib.Consensus.Proofs.DirectSafety.Fields
import EthLib.Consensus.Proofs.Transition.ValidatorKeys

/-!
# The quorum of a call drifts by at most its pin reserve, on another branch

A call of the fast confirmation rule reads the pulled-up head state R of an honest store.

A counting state C of another honest store may lie on another branch since the finalized checkpoint.

The two branches leave one split state, at or after the finalized checkpoint's epoch.

This file bounds the drift of the quorum from R to C by `pinReserve`.

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

The reserve reads its rates at the call's total, so it needs every total on both branches nearby.

`aprioriGuardAt` at the finalized state bounds each total of a branch from it.

It bounds each such total by a floor and a ceiling.

Before Gloas, twice the last ceiling of the window is at most three times its last floor.

So two totals of the window are within three halves of each other.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-- A run from a state without a property to a state with it splits at a step that gains it. -/
private theorem Run.split_at_flip {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (P : ForkedBeaconState preset → Prop) (missing : ¬P x) (held : P y) :
    ∃ (m n : ForkedBeaconState preset) (pre : Run config checks x m)
      (step : Step config checks m n) (post : Run config checks n y),
      tail = (pre.snoc step).append post ∧ ¬P m ∧ P n := by
  induction tail with
  | nil => exact absurd held missing
  | @snoc middle last pre step ih =>
    by_cases inside : P middle
    · obtain ⟨m, n, a, one, rest, split, hm, hn⟩ := ih inside
      refine ⟨m, n, a, one, rest.snoc step, ?_, hm, hn⟩
      rw [split]
      rfl
    · exact ⟨middle, last, pre, step, .nil, rfl, inside, held⟩

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
private theorem fresh_unslashed {g m n : ForkedBeaconState preset}
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
private theorem slashed_waits {g : ForkedBeaconState preset}
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
    have unslashedAtN := fresh_unslashed (toSplit.append pre) step genesis
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
private def passPenaltyRate (config : Config) (z : ForkedBeaconState preset) (v : ℕ) : ℕ :=
  let total := max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    (∑ i ∈ (Finset.range z.state.validators.data.size).filter
        (fun i => isActiveAt z.state (getCurrentEpoch z.state) i = true),
      ((z.state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0)
  let score := if altair : .altair ≤ z.fork then
      (((z.state.inactivityScores altair).data[v]?).map (·.toNat)).getD 0 else 0
  (TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat) * preset.BASE_REWARD_FACTOR.toNat *
      effectiveAt z v / (WEIGHT_DENOMINATOR.toNat * total.sqrt) +
    effectiveAt z v * (score + config.INACTIVITY_SCORE_BIAS.toNat) /
      (config.INACTIVITY_SCORE_BIAS.toNat *
        (parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat)

/-- Events with no penalty or inactivity source debit no key as a penalty. -/
private theorem penaltyDebit_sum_zero {events : List (BalanceEvent preset)}
    (free : PenaltyFree events) (v : ℕ) : (events.map (penaltyDebit v)).sum = 0 :=
  List.sum_eq_zero fun _ member => by
    obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
    simp [penaltyDebit, (free e inside).1, (free e inside).2]

/-- The penalties of one key in one segment of a branch fit its pass rate.

This holds if the segment ends an epoch, and the penalties are zero otherwise.

The rate is asked only at the last pass state, and only when it has a total active balance.

Every step of the segment starts at the epoch of its start `m`.

Inside the epoch only blocks run, and they record no penalty.

The slot that ends the epoch runs the rewards pass, read at its last state.

So a segment that stays in its epoch pays nothing. -/
private theorem segment_passDebit_le_guarded {m n : ForkedBeaconState preset}
    (mid : Run config checks m n) (early : n.fork < .glamsterdam) (altair : .altair ≤ m.fork)
    (high : ℕ) (endEpoch : (getCurrentEpoch n.state).toNat ≤ high + 1)
    (starts : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      mid.Contains step → getCurrentEpoch u.state = getCurrentEpoch m.state)
    {v : ℕ} (inside : v < m.state.validators.data.size) (pen : ℕ)
    (rate : ∀ {z : ForkedBeaconState preset} (pre : Run config checks m z)
      (ok : advanceSlotAcross config checks z = .ok n), mid = pre.snoc (Step.slot ok) →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch n.state).toNat →
      (∃ total, getTotalActiveBalance z.state = .ok total) → passPenaltyRate config z v ≤ pen)
    {found : List (BalanceEvent preset)} (replayed : mid.balanceEvents high = .ok found) :
    (found.map (penaltyDebit v)).sum ≤
      if getCurrentEpoch m.state < getCurrentEpoch n.state then pen else 0 := by
  by_cases same : getCurrentEpoch n.state = getCurrentEpoch m.state
  · -- A segment inside its epoch runs only blocks, which record no penalty.
    have free := (epoch_sync_data mid altair early same high replayed).2.1
    rw [penaltyDebit_sum_zero free]
    exact Nat.zero_le _
  cases mid with
  | nil => exact absurd rfl same
  | @snoc u _ inner step =>
  have uEarly : u.fork < .glamsterdam := Nat.lt_of_le_of_lt step.chainStep.fork_le early
  have uEpoch : getCurrentEpoch u.state = getCurrentEpoch m.state := starts step (.last _ _)
  have crossing : getCurrentEpoch u.state < getCurrentEpoch n.state :=
    UInt64.lt_of_le_of_ne step.chainStep.currentEpoch_le
      (fun equal => same (equal.symm.trans uEpoch))
  rw [ite_eq_left (uEpoch ▸ crossing)]
  -- The last step leaves the epoch, so it is the slot that ends it.
  obtain ⟨boundary, rfl⟩ : ∃ boundary, step = .slot boundary := by
    cases step with
    | block engine signed due ok =>
      exact absurd (by simp only [getCurrentEpoch, (frame_processBlock
        (applySignedBlock_ok ok).2.1).slot]) (UInt64.ne_of_lt crossing).symm
    | slot ok => exact ⟨ok, rfl⟩
  obtain ⟨added, addedOk⟩ := (Step.slot boundary).balanceEvents_ok early
  obtain ⟨during, duringOk⟩ := inner.balanceEvents_ok uEarly high
  have split : found = during ++ added := by
    simp only [Run.balanceEvents, duringOk, addedOk, bind, Except.bind,
      show (getCurrentEpoch u.state).toNat ≤ high + 1 by
        have := UInt64.lt_iff_toNat_lt.mp crossing; omega,
      ↓reduceIte, pure, Except.pure, Except.ok.injEq] at replayed
    exact replayed.symm
  subst split
  have free := (epoch_sync_data inner altair uEarly uEpoch high duringOk).2.1
  simp only [List.map_append, List.sum_append, penaltyDebit_sum_zero free, Nat.zero_add]
  -- The slot records the epoch passes, then the upgrades, which are fork crossings.
  obtain ⟨advanced, cached, crossings, -, -, cachedOk, crossingOk, kind⟩ :=
    Step.balanceEvents_slot boundary early addedOk
  have crossed := upgradeBalanceReplay_crossing crossingOk
  have crossingsFree : PenaltyFree crossings := fun e member => by
    simp [crossed e member]
  rcases kind with ⟨-, rfl⟩ | ⟨middle, -, recorded, recordOk, -, -, -, rfl, -⟩
  · rw [penaltyDebit_sum_zero crossingsFree]
    exact Nat.zero_le _
  have altairU : .altair ≤ u.fork := Nat.le_trans altair (fork_le_of_chainSteps inner.chainSteps)
  obtain ⟨just, pass, rewarded, later, justified, scored, rewardedOk, recordedEq, laterSources,
    -⟩ := epochReplay_events altairU (epochBalanceReplay_trace recordOk)
  simp only at recordedEq
  subst recordedEq
  have laterFree : PenaltyFree later := fun e member => by
    rcases laterSources e member with s | s | s <;> simp [s]
  simp only [List.map_append, List.sum_append, penaltyDebit_sum_zero laterFree,
    penaltyDebit_sum_zero crossingsFree, Nat.add_zero]
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
    ⟨total, -, passTotal, -⟩ | quiet
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
    (UInt64.lt_iff_toNat_lt.mp crossing) ⟨total, totalU⟩))
  -- The pass's reads are those of `u`.
  have weight : eligibleWeight pass v ≤ effectiveAt u v := by
    unfold eligibleWeight
    simp only [validators, effectiveAt]
    split <;> [split <;> simp_all; simp]
  have totalValue : total.toNat = max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      (∑ i ∈ (Finset.range u.state.validators.data.size).filter
          (fun i => isActiveAt u.state (getCurrentEpoch u.state) i = true),
        ((u.state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0) := by
    rw [getTotalActiveBalance_toNat passTotal, ← passEpoch]
    unfold activeBalanceTotal
    simp only [isActiveAt, validators]
    congr
  unfold passPenaltyRate
  dsimp only
  rw [← totalValue, ← scoreDef]
  apply Nat.add_le_add
  · apply Nat.div_le_div_right
    exact Nat.mul_le_mul_left _ weight
  · apply Nat.div_le_div_right
    exact Nat.mul_le_mul_right _ weight

/-- The penalties of one key in one segment of a branch fit its pass rate.

They are zero if the segment does not end an epoch.

Every step of the segment starts at the epoch of its start `m`.

Inside the epoch only blocks run, and they record no penalty.

The slot that ends the epoch runs the rewards pass, read at its last state.

So a segment that stays in its epoch pays nothing. -/
private theorem segment_passDebit_le {m n : ForkedBeaconState preset}
    (mid : Run config checks m n) (early : n.fork < .glamsterdam) (altair : .altair ≤ m.fork)
    (high : ℕ) (endEpoch : (getCurrentEpoch n.state).toNat ≤ high + 1)
    (starts : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      mid.Contains step → getCurrentEpoch u.state = getCurrentEpoch m.state)
    {v : ℕ} (inside : v < m.state.validators.data.size) (pen : ℕ)
    (rate : ∀ {z : ForkedBeaconState preset} (pre : Run config checks m z)
      (post : Run config checks z n), mid = pre.append post →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch n.state).toNat →
      passPenaltyRate config z v ≤ pen)
    {found : List (BalanceEvent preset)} (replayed : mid.balanceEvents high = .ok found) :
    (found.map (penaltyDebit v)).sum ≤
      if getCurrentEpoch m.state < getCurrentEpoch n.state then pen else 0 := by
  refine segment_passDebit_le_guarded mid early altair high endEpoch starts inside pen
    (fun pre ok split before _ => rate pre (Run.nil.snoc (Step.slot ok)) split before) replayed

/-- The first `k` of the first `j` terms each count `pen`. -/
private theorem sum_range_ite_lt (pen k : ℕ) :
    ∀ j, ((List.range j).map fun t => if t < k then pen else 0).sum = min j k * pen
  | 0 => by simp
  | j + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_ite_lt pen k j]
    by_cases below : j < k
    · simp [below, Nat.min_eq_left (Nat.le_of_lt below), Nat.min_eq_left (Nat.succ_le_of_lt below),
        Nat.succ_mul]
    · have atLeast : k ≤ j := Nat.le_of_not_lt below
      simp [below, Nat.min_eq_right atLeast, Nat.min_eq_right (Nat.le_succ_of_le atLeast)]

/-- The terms below an index count their value, and the others count zero. -/
private theorem sum_range_ite_lt_fn (pen : ℕ → ℕ) (k : ℕ) :
    ∀ j, ∑ t ∈ Finset.range j, (if t < k then pen t else 0) = ∑ t ∈ Finset.range (min j k), pen t
  | 0 => by simp
  | j + 1 => by
    rw [Finset.sum_range_succ, sum_range_ite_lt_fn pen k j]
    by_cases below : j < k
    · simp [below, Nat.min_eq_left (Nat.le_of_lt below),
        Nat.min_eq_left (Nat.succ_le_of_lt below), Finset.sum_range_succ]
    · have atLeast : k ≤ j := Nat.le_of_not_lt below
      simp [below, Nat.min_eq_right atLeast, Nat.min_eq_right (Nat.le_succ_of_le atLeast)]

/-- A sum over an interval of naturals is the sum over the offsets from its start. -/
private theorem sum_Ico_offsets (pen : ℕ → ℕ) (a b : ℕ) :
    ∑ t ∈ Finset.Ico a b, pen t = ∑ t ∈ Finset.range (b - a), pen (a + t) := by
  refine Finset.sum_nbij' (fun t => t - a) (fun t => a + t) ?_ ?_ ?_ ?_ ?_
  · intro t member
    simp only [Finset.mem_Ico, Finset.mem_range] at member ⊢
    omega
  · intro t member
    simp only [Finset.mem_Ico, Finset.mem_range] at member ⊢
    omega
  · intro t member
    simp only [Finset.mem_Ico] at member
    omega
  · intro t member
    omega
  · intro t member
    simp only [Finset.mem_Ico] at member
    congr 1
    omega

/-- A sum over a list of the first terms is the sum over the finite set of the first terms. -/
private theorem list_range_sum (pen : ℕ → ℕ) :
    ∀ j, ((List.range j).map pen).sum = ∑ t ∈ Finset.range j, pen t
  | 0 => by simp
  | j + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_range_sum pen j,
      Finset.sum_range_succ]
    simp

/-- A state of a segment that is followed by a step of the segment is in the epoch of its start. -/
private theorem segment_epoch_eq {m n z : ForkedBeaconState preset}
    (mid : Run config checks m n) (pre : Run config checks m z) (post : Run config checks z n)
    (split : mid = pre.append post)
    (starts : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      mid.Contains step → getCurrentEpoch u.state = getCurrentEpoch m.state)
    (before : (getCurrentEpoch z.state).toNat < (getCurrentEpoch n.state).toNat) :
    getCurrentEpoch z.state = getCurrentEpoch m.state := by
  subst split
  cases post with
  | nil => exact absurd before (Nat.lt_irrefl _)
  | @snoc u _ inner step =>
    have atU : getCurrentEpoch u.state = getCurrentEpoch m.state :=
      starts step (.last (pre.append inner) step)
    exact UInt64.le_antisymm
      (atU ▸ currentEpoch_le_of_chainSteps inner.chainSteps)
      (currentEpoch_le_of_chainSteps pre.chainSteps)

/-- The penalties of one key over a branch from Altair are at most the sum of its pass rates.

The rate must hold at each state of the branch before the epoch of its end, at that state's epoch.

The branch ends `epoch y - epoch x` epochs, and each runs one rewards pass.

The cut induction of the a priori bound, `run_cuts_le`, sums the segments. -/
private theorem Run.passDebit_le_rates {x y : ForkedBeaconState preset}
    (tail : Run config checks x y)
    (early : y.fork < .glamsterdam) (altair : .altair ≤ x.fork) (high : ℕ)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    {v : ℕ} (inside : v < x.state.validators.data.size) (pen : ℕ → ℕ)
    (rate : ∀ {z : ForkedBeaconState preset} (pre : Run config checks x z)
      (post : Run config checks z y), tail = pre.append post →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch y.state).toNat →
      passPenaltyRate config z v ≤ pen (getCurrentEpoch z.state).toNat)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    (events.map (penaltyDebit v)).sum ≤
      ∑ t ∈ Finset.Ico (getCurrentEpoch x.state).toNat (getCurrentEpoch y.state).toNat, pen t := by
  have total := run_cuts_le high tail early
    (fun z => passPenaltyRate config z v ≤ pen (getCurrentEpoch z.state).toNat)
    (penaltyDebit v)
    (fun t => if t < ix x y then pen ((getCurrentEpoch x.state).toNat + t) else 0) rate
    (fun {m n} toM mid rest starts rates {found} found_ok => by
      have nEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) early
      have ny := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest.chainSteps)
      have segment := segment_passDebit_le mid nEarly
        (Nat.le_trans altair (fork_le_of_chainSteps toM.chainSteps)) high (by omega) starts
        (Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps toM.chainSteps))
        (pen (getCurrentEpoch m.state).toNat)
        (fun {z} preZ postZ split before => by
          have same := segment_epoch_eq mid preZ postZ split starts before
          rw [← same]
          exact rates preZ postZ split before)
        found_ok
      refine segment.trans ?_
      split
      · rename_i before
        have := UInt64.lt_iff_toNat_lt.mp before
        have xm := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps toM.chainSteps)
        simp only [ix]
        rw [ite_eq_left (by omega), Nat.add_sub_cancel' xm]
      · exact Nat.zero_le _)
    (ix x y + 1) (fun step member => steps_before_end tail step member) replayed
  rw [list_range_sum, sum_range_ite_lt_fn (fun t => pen ((getCurrentEpoch x.state).toNat + t))
    (ix x y) (ix x y + 1), Nat.min_eq_right (Nat.le_succ _)] at total
  rw [sum_Ico_offsets]
  simpa [ix] using total

/-- The penalties of one key over a branch from Altair are at most its pass rate per epoch ended.

The rate must hold at each state of the branch before the epoch of its end.

The branch ends `epoch y - epoch x` epochs, and each runs one rewards pass.

The cut induction of the a priori bound, `run_cuts_le`, sums the segments. -/
private theorem Run.passDebit_le {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (early : y.fork < .glamsterdam) (altair : .altair ≤ x.fork) (high : ℕ)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    {v : ℕ} (inside : v < x.state.validators.data.size) (pen : ℕ)
    (rate : ∀ {z : ForkedBeaconState preset} (pre : Run config checks x z)
      (post : Run config checks z y), tail = pre.append post →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch y.state).toNat →
      passPenaltyRate config z v ≤ pen)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    (events.map (penaltyDebit v)).sum ≤
      ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) * pen := by
  simpa using Run.passDebit_le_rates tail early altair high endEpoch inside (fun _ => pen) rate
    replayed

/-- The sync debit of one key in one event. -/
private def syncDebit (v : ℕ) (event : BalanceEvent preset) : ℕ :=
  if event.source = .sync then actualBalanceAt event.before v - actualBalanceAt event.after v else 0

/-- The sync credit of a key in one event. -/
private def syncCredit (v : ℕ) (event : BalanceEvent preset) : ℕ :=
  if event.source = .sync then actualBalanceAt event.after v - actualBalanceAt event.before v else 0

/-- The balance of a key that stays unslashed falls over a branch only by its debits, as events.

It starts from the smaller of its balance and its largest effective balance.

The debits are the penalties, the sync penalties and the partial withdrawals of its events.

The guards are those of the per-key floor of the a priori bound, `FloorTrace.run_of_le_cap`.

A key with no activation epoch is allowed if the branch starts from Fulu or later. -/
private theorem Run.balanceFloor_events_or_fulu {g x y : ForkedBeaconState preset}
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
        (events.map (syncDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum := by
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
      (events.map (penaltyDebit v.toNat)).sum + (events.map (syncDebit v.toNat)).sum := by
    rw [← List.sum_map_add]
    rfl
  rw [balance, debt, split] at floor
  omega

/-- The balance of a key that stays unslashed falls over a branch only by its debits.

It starts from the smaller of its balance and its largest effective balance.

A sweep of its excess and a switch to compounding leave at least that much.

The debits are its passes, its sync penalties and its partial withdrawals.

The passes are at most its pass rates at the epochs ended.

The guards are those of the per-key floor of the a priori bound, `FloorTrace.run_of_le_cap`.

A key with no activation epoch is allowed if the branch starts from Fulu or later. -/
private theorem Run.balanceFloor_rates_or_fulu {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (early : y.fork < .glamsterdam) (altair : .altair ≤ x.fork) (high : ℕ)
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
    (pen : ℕ → ℕ)
    (rate : ∀ {z : ForkedBeaconState preset} (pre : Run config checks x z)
      (post : Run config checks z y), tail = pre.append post →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch y.state).toNat →
      passPenaltyRate config z v.toNat ≤ pen (getCurrentEpoch z.state).toNat)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    min (actualBalanceAt x v.toNat) (withdrawalMaxEffectiveBalance preset x.fork val).toNat ≤
      actualBalanceAt y v.toNat +
        ∑ t ∈ Finset.Ico (getCurrentEpoch x.state).toNat (getCurrentEpoch y.state).toNat, pen t +
        (events.map (syncDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum := by
  have floor := Run.balanceFloor_events_or_fulu shared tail genesis caps delay early high endEpoch
    v val initial unslashed activated quotient positive guards stays replayed
  have inside := (Array.getElem?_eq_some_iff.mp initial).1
  have passes := Run.passDebit_le_rates tail early altair high endEpoch inside pen rate replayed
  omega

/-- The balance of a key that stays unslashed falls over a branch only by its debits.

It starts from the smaller of its balance and its largest effective balance.

A sweep of its excess and a switch to compounding leave at least that much.

The debits are its passes, its sync penalties and its partial withdrawals.

The passes are at most its pass rates at the epochs ended.

The guards are those of the per-key floor of the a priori bound, `FloorTrace.run_of_le_cap`. -/
private theorem Run.balanceFloor_rates {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (early : y.fork < .glamsterdam) (altair : .altair ≤ x.fork) (high : ℕ)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (v : ValidatorIndex) (val : Validator) (initial : x.state.validators.data[v.toNat]? = some val)
    (unslashed : val.slashed = false) (activated : val.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (quotient : ℕ) (positive : 0 < quotient)
    (guards : ∀ {m n : ForkedBeaconState preset} (pre : Run config checks x m)
      (step : Step config checks m n) (post : Run config checks n y),
      (pre.snoc step).append post = tail → ∀ w, n.state.validators.data[v.toNat]? = some w →
      high + 1 < w.exitEpoch.toNat ∧
      (getCurrentEpoch m.state).toNat < (getCurrentEpoch x.state).toNat +
        preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
          (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat ∧
      quotient ≤ (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
      ∀ events, step.balanceEvents = .ok events → ∀ e ∈ events, e.source ≠ .crossing)
    (stays : ∀ w, y.state.validators.data[v.toNat]? = some w → w.slashed = false)
    (pen : ℕ → ℕ)
    (rate : ∀ {z : ForkedBeaconState preset} (pre : Run config checks x z)
      (post : Run config checks z y), tail = pre.append post →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch y.state).toNat →
      passPenaltyRate config z v.toNat ≤ pen (getCurrentEpoch z.state).toNat)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    min (actualBalanceAt x v.toNat) (withdrawalMaxEffectiveBalance preset x.fork val).toNat ≤
      actualBalanceAt y v.toNat +
        ∑ t ∈ Finset.Ico (getCurrentEpoch x.state).toNat (getCurrentEpoch y.state).toNat, pen t +
        (events.map (syncDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum :=
  Run.balanceFloor_rates_or_fulu shared tail genesis caps delay early altair high endEpoch v val
    initial unslashed (Or.inl activated) quotient positive
    (fun pre step post split w found => by
      obtain ⟨retained, rest⟩ := guards pre step post split w found
      exact ⟨Or.inl retained, rest⟩) stays pen rate replayed

/-- The balance of a key that stays unslashed falls over a branch only by its debits.

It starts from the smaller of its balance and its largest effective balance.

A sweep of its excess and a switch to compounding leave at least that much.

The debits are its passes, at most its pass rate per epoch ended.

They also hold its sync penalties and the partial withdrawals that the branch pays it.

The guards are those of the per-key floor of the a priori bound, `FloorTrace.run_of_le_cap`. -/
private theorem Run.balanceFloor {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (early : y.fork < .glamsterdam) (altair : .altair ≤ x.fork) (high : ℕ)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (v : ValidatorIndex) (val : Validator) (initial : x.state.validators.data[v.toNat]? = some val)
    (unslashed : val.slashed = false) (activated : val.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (quotient : ℕ) (positive : 0 < quotient)
    (guards : ∀ {m n : ForkedBeaconState preset} (pre : Run config checks x m)
      (step : Step config checks m n) (post : Run config checks n y),
      (pre.snoc step).append post = tail → ∀ w, n.state.validators.data[v.toNat]? = some w →
      high + 1 < w.exitEpoch.toNat ∧
      (getCurrentEpoch m.state).toNat < (getCurrentEpoch x.state).toNat +
        preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
          (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat ∧
      quotient ≤ (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
      ∀ events, step.balanceEvents = .ok events → ∀ e ∈ events, e.source ≠ .crossing)
    (stays : ∀ w, y.state.validators.data[v.toNat]? = some w → w.slashed = false)
    (pen : ℕ)
    (rate : ∀ {z : ForkedBeaconState preset} (pre : Run config checks x z)
      (post : Run config checks z y), tail = pre.append post →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch y.state).toNat →
      passPenaltyRate config z v.toNat ≤ pen)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    min (actualBalanceAt x v.toNat) (withdrawalMaxEffectiveBalance preset x.fork val).toNat ≤
      actualBalanceAt y v.toNat +
        ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) * pen +
        (events.map (syncDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum := by
  have rates := Run.balanceFloor_rates shared tail genesis caps delay early altair high endEpoch v
    val initial unslashed activated quotient positive guards stays (fun _ => pen) rate replayed
  simpa using rates

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

/-- The partial payments to one key over a branch from Electra fit its entries due by the cutoff.

These are its entries of the queue at the start.

The cutoff is within the withdrawal delay of the start.

An entry appended along the branch is due no earlier than the delay after the start. -/
private theorem Run.partialDebit_le {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (high cutoff : ℕ) (endpoint : (getCurrentEpoch y.state).toNat ≤ cutoff)
    (short : cutoff < (getCurrentEpoch x.state).toNat +
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (v : ValidatorIndex) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events) :
    (events.map (floorPartialDebit v)).sum ≤
      ((((x.state.pendingPartialWithdrawals electra).data.toList.filter
        fun entry => decide (entry.validatorIndex = v)).filter
          (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff)).map (·.amount.toNat)).sum := by
  obtain ⟨added, late, bound⟩ :=
    run_partial_queue_kept (partialCost_key v) high cutoff electra tail early replayed endpoint
  have none : ((added.filter fun entry => decide (entry.validatorIndex = v)).filter
      (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro entry member
    have := late entry (List.mem_of_mem_filter member)
    simp only [decide_eq_true_eq]
    omega
  rw [none] at bound
  simpa using bound

/-! ## The band of totals from the guard at the finalized state -/

section Band

open DirectSafety.Apriori

/-- From Electra, the ceiling of a window grows with the epoch of the window. -/
private theorem stakeCeilingAt_mono {x : ForkedBeaconState preset} {high : ℕ}
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
private theorem stakeFloorAt_anti {x : ForkedBeaconState preset} {high : ℕ} {s t : ℕ}
    (le : s ≤ t) : stakeFloorAt config x high t ≤ stakeFloorAt config x high s := by
  induction le with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    refine Nat.le_trans ?_ ih
    simp only [stakeFloorAt, stakeFloor, stakeFloorPath]
    omega

/-- From Electra and before Gloas, take a state reached from a guarded state within its window.

Its total is between the window's last floor and last ceiling.

The window's last index is the epoch after `high`, counted from the guarded state's epoch. -/
private theorem total_within_guard {g x z : ForkedBeaconState preset} {high : ℕ}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : DirectSafety.Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (electra : .pectra ≤ x.fork) (guard : aprioriGuardAt config x high)
    (run : Run config checks x z) (early : z.fork < .glamsterdam)
    (within : (getCurrentEpoch z.state).toNat ≤ high + 1) {total : Gwei}
    (totalOk : getTotalActiveBalance z.state = .ok total) :
    let last := high + 1 - (getCurrentEpoch x.state).toNat
    stakeFloorAt config x high last ≤ total.toNat ∧
      total.toNat ≤ stakeCeilingAt config x high last := by
  intro last
  have index : ix x z ≤ last := by
    simp only [ix, last]
    omega
  obtain ⟨ceiling, -, floor⟩ := ceilingFloor_electra shared run high
    ⟨genesis, parameters, caps, aligned, early, within, guard⟩ twoSlots electra
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps run.chainSteps) early
  have unit := (ceiling_unit_of_guard shared genesis aligned xEarly electra guard).trans
    (stakeCeilingAt_mono electra (Nat.zero_le last))
  refine ⟨(stakeFloorAt_anti index).trans (floor total totalOk), ?_⟩
  obtain ⟨-, -, value⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok totalOk)
  rw [value]
  exact max_le unit (Nat.le_trans ceiling (stakeCeilingAt_mono electra index))

/-- From Electra and before Gloas, take two states reached from a guarded state in its window.

Their totals are within three halves of each other.

Both lie between the window's last floor and ceiling.

The guard asks that twice that ceiling be at most three times that floor. -/
private theorem total_band_of_guard {g x y z : ForkedBeaconState preset} {high : ℕ}
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
  have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
  have zero : preElectraEpochs config x high = 0 := by simp [preElectraEpochs, notBefore]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ratioGuard, -⟩ := id guard
  rw [zero] at ratioGuard
  have ratio := ratioGuard (high + 1 - (getCurrentEpoch x.state).toNat) (Nat.zero_le _)
    (by unfold driftHorizon; omega)
  obtain ⟨yLow, -⟩ := total_within_guard shared genesis parameters caps aligned twoSlots electra
    guard toY yEarly yWithin yOk
  obtain ⟨-, zHigh⟩ := total_within_guard shared genesis parameters caps aligned twoSlots electra
    guard toZ zEarly zWithin zOk
  simp only [stakeCeilingAt, stakeFloorAt, zero] at yLow zHigh ⊢
  omega

/-- The preset facts that the producer of the pin needs.

Each field is a fact about the preset alone, and a deployed preset has it. -/
private structure PinPresetFacts (preset : Preset) : Prop where
  /-- (preset fact) One epoch's base reward factor at an increment is at least `2 ^ 33`. -/
  room : 2 ^ 33 ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat
  /-- (preset fact) The downward band is below an increment. -/
  below : preset.downwardBand < preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  /-- (preset fact) An increment is at least 900 times the slashings vector. -/
  rounding : 900 * preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  /-- (preset fact) An increment is at least 14 times the slashing quotient. -/
  slash : 14 * (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat ≤
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  /-- (preset fact) The slashings vector has at least four epochs. -/
  vector : 4 ≤ preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat
  /-- (preset fact) The base reward factor is positive. -/
  reward : 1 ≤ preset.BASE_REWARD_FACTOR.toNat
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
  /-- (preset fact) At every fork the whistleblower quotient is at least two. -/
  whistleblower : ∀ fork : Fork,
    2 ≤ (EthLib.Consensus.parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  /-- (preset fact) The increment times the base reward factor is `2 ^ 35` or more, never small. -/
  rewardScale : 2 ^ 35 ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat
  /-- (preset fact) An increment is at least `10 ^ 8` gwei, which rules out a small increment. -/
  incrementSize : 10 ^ 8 ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat

/-- The mainnet preset has the preset facts of the pin. -/
private theorem PinPresetFacts.mainnet : PinPresetFacts Preset.mainnet :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, fun fork => by cases fork <;> decide,
    fun fork => by cases fork <;> decide, by decide, by decide⟩

/-- The minimal preset has the preset facts of the pin. -/
private theorem PinPresetFacts.minimal : PinPresetFacts Preset.minimal :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, fun fork => by cases fork <;> decide,
    fun fork => by cases fork <;> decide, by decide, by decide⟩

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
  obtain ⟨-, -, -, -, -, -, -, -, -, -, window, -, ratioGuard, -⟩ := id guard
  rw [zero] at ratioGuard
  have ratio := ratioGuard (high + 1 - (getCurrentEpoch x.state).toNat) (Nat.zero_le _)
    (by unfold driftHorizon; omega)
  have unit := (ceiling_unit_of_guard shared genesis aligned xEarly electra guard).trans
    (stakeCeilingAt_mono electra (Nat.zero_le (high + 1 - (getCurrentEpoch x.state).toNat)))
  have anti := stakeFloorAt_anti (config := config) (x := x) (high := high)
    (Nat.zero_le (high + 1 - (getCurrentEpoch x.state).toNat))
  have rounding := facts.rounding
  have slash := facts.slash
  simp only [stakeCeilingAt, stakeFloorAt, zero] at unit anti ratio ⊢
  unfold driftHorizon at window
  constructor <;> omega

/-- From Electra and before Gloas, the floor of the window at its start leaves room for the window.

It is the first conclusion of `first_floor_of_guard`. -/
private theorem room_of_guard {g x : ForkedBeaconState preset} {high : ℕ}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (aligned : MaxEffectiveBalancesAligned preset)
    (xEarly : x.fork < .glamsterdam)
    (electra : .pectra ≤ x.fork) (guard : aprioriGuardAt config x high)
    (facts : PinPresetFacts preset) :
    600 * (high + 2 - (getCurrentEpoch x.state).toNat) ≤ stakeFloorAt config x high 0 :=
  (first_floor_of_guard shared genesis aligned xEarly electra guard facts).1

/-- From Electra and before Gloas, the floor of the window at its start is large.

It is at least nine slashing quotients, the second conclusion of `first_floor_of_guard`. -/
private theorem big_of_guard {g x : ForkedBeaconState preset} {high : ℕ}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (aligned : MaxEffectiveBalancesAligned preset)
    (xEarly : x.fork < .glamsterdam)
    (electra : .pectra ≤ x.fork) (guard : aprioriGuardAt config x high)
    (facts : PinPresetFacts preset) :
    9 * (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat ≤
      stakeFloorAt config x high 0 :=
  (first_floor_of_guard shared genesis aligned xEarly electra guard facts).2

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

section GroupB

/-! ## PinSlashing -/

namespace PinSplit

open Base Uint64 Models DirectSafety

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-- The credit of key `i` in one replayed event. -/
private def keyCredit (i : ℕ) (e : BalanceEvent preset) : ℕ :=
  actualBalanceAt e.after i - actualBalanceAt e.before i

/-- The credits to the key in one step, from the sources that count at that kind of step. -/
private def stepCredit (blockP slotP : BalanceSource → Bool) (v : ℕ)
    {x y : ForkedBeaconState preset} (step : Step config checks x y) : ℕ :=
  let events := step.balanceEvents.toOption.getD []
  match step with
  | .slot _ => ((events.filter (slotP ·.source)).map (keyCredit v)).sum
  | .block .. => ((events.filter (blockP ·.source)).map (keyCredit v)).sum

/-- The credits to the key over a run, and the number of block steps that credit it.

The steps count from the one whose start epoch is at most `high + 1`, as in `Run.balanceEvents`. -/
private def creditScan (blockP slotP : BalanceSource → Bool) (v high : ℕ)
    {x : ForkedBeaconState preset} :
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

/-- One slashing credits at most the slashed key's effective balance over the quotient.

The credits go to the proposer and the whistleblower together. -/
private theorem slashValidator_credits_le {state after : BeaconState preset fork}
    {slashed : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (computed : slashValidator config state slashed whistleblower = .ok after) :
    ∑ i ∈ Finset.range after.balances.data.size,
        (((after.balances.data[i]?).map (·.toNat)).getD 0 -
          ((state.balances.data[i]?).map (·.toNat)).getD 0) ≤
      balanceAt state slashed.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat := by
  obtain ⟨exited, -, -, -, -, -, -, -, -, -, -, -, exitedOk, -⟩ := slashValidator_ok computed
  obtain ⟨v, found, -⟩ := initiateValidatorExit_ok exitedOk
  have bound := (initial_slashing_bounds state after slashed whistleblower v found computed).2
  have effective : balanceAt state slashed.toNat = v.effectiveBalance.toNat := by
    simp [balanceAt, getValidator_eq_ok_iff.mp found]
  rw [effective]
  exact bound

/-- A slashing of a key that has not started to exit starts its exit through the exit queue.

The exit epoch of the key is then not the far future, since the delay is positive. -/
private theorem slashValidator_exit_churn {state after : BeaconState preset fork}
    (electra : .pectra ≤ fork) {slashed : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (computed : slashValidator config state slashed whistleblower = .ok after)
    (fresh :
      ((state.validators.data[slashed.toNat]?).map (·.exitEpoch)).getD 0 = FAR_FUTURE_EPOCH) :
    ∃ middle, initiateValidatorExit config state slashed = .ok middle ∧
      (middle.validators.data[slashed.toNat]?).any (·.exitEpoch ≠ FAR_FUTURE_EPOCH) := by
  have _ := electra
  obtain ⟨exited, -, -, -, -, -, -, -, -, -, -, -, exitedOk, -⟩ := slashValidator_ok computed
  refine ⟨exited, exitedOk, ?_⟩
  obtain ⟨v, found, started | ⟨far, queued, exitEpoch, withdrawable, queue, summed, set⟩⟩ :=
    initiateValidatorExit_ok exitedOk
  · have read := getValidator_eq_ok_iff.mp found
    simp [read] at fresh
    exact absurd fresh started.1
  · obtain ⟨inside, rfl⟩ := setValidator_ok set
    have sum := (addChecked_ok_iff.mp summed).1
    have finite : exitEpoch ≠ FAR_FUTURE_EPOCH := by
      intro same
      rw [same] at sum
      have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
      omega
    simp [BeaconState.putValidator, finite]

/-- Events within their credit limits credit the slashing events at most their limits. -/
private theorem slashing_credits_le_limits (events : List (BalanceEvent preset))
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

/-- Along a run from Electra, each key is slashed at most once.

So its whistleblower reward is paid once, at its effective balance when it is slashed. -/
private theorem Run.slashed_once {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (caps : CapOrder preset) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (high : ℕ)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    ((events.filter (·.source = .slashings)).map BalanceEvent.credits).sum ≤
      ∑ i ∈ Finset.range y.state.validators.data.size,
        if ((x.state.validators.data[i]?).map (·.slashed)).getD false = false ∧
            ((y.state.validators.data[i]?).map (·.slashed)).getD false = true
        then (((tail.balancePath.map fun z => effectiveAt z i).foldr max 0) /
            (parameters preset y.fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)
        else 0 := by
  obtain ⟨found, foundOk, bounded⟩ := Run.balanceEvents_bounded shared tail genesis early high
  rw [replayed] at foundOk
  cases foundOk
  refine (slashing_credits_le_limits events fun e member => (bounded e member).1).trans ?_
  let keys := (Finset.range y.state.validators.data.size).filter fun i =>
    ((x.state.validators.data[i]?).map (·.slashed)).getD false = false ∧
      ((y.state.validators.data[i]?).map (·.slashed)).getD false = true
  let charge (i : ℕ) : ℕ := ((tail.balancePath.map fun z => effectiveAt z i).foldr max 0) /
    (parameters preset y.fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  rw [← Finset.sum_filter]
  refine Apriori.Internal.slashing_credits_le shared tail genesis early caps.compounding high
    endEpoch keys charge ?_ replayed
  intro a b step contained i inside marked
  obtain ⟨pre, post, split⟩ := tail.contains_split step contained
  have flags : (a.state.validators.data[i]?.map (·.slashed)).getD false = false ∧
      (b.state.validators.data[i]?.map (·.slashed)).getD false = true := by
    simpa only [Bool.and_eq_true, Bool.not_eq_true'] using marked
  have last : (y.state.validators.data[i]?.map (·.slashed)).getD false = true := by
    cases found : b.state.validators.data[i]? with
    | none => simp [found] at flags
    | some v =>
      have was : v.slashed = true := by simpa [found] using flags.2
      obtain ⟨w, read, flag⟩ := post.slashedPersistence i v found was
      simp [read, flag]
  have first : (x.state.validators.data[i]?.map (·.slashed)).getD false = false := by
    cases found : x.state.validators.data[i]? with
    | none => simp
    | some v =>
      cases flag : v.slashed with
      | false => simp [flag]
      | true =>
        obtain ⟨w, read, kept⟩ := pre.slashedPersistence i v found flag
        simp [read, kept] at flags
  have onPath : a ∈ tail.balancePath := by
    rw [split, Run.balancePath_append]
    have head := Step.balancePath_ends step
    have inStep := List.mem_of_mem_head? head.1
    simp [Run.balancePath, inStep]
  have atLeast : a.fork ≥ .pectra := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
  have atMost : a.fork ≤ y.fork :=
    Nat.le_trans step.chainStep.fork_le (fork_le_of_chainSteps post.chainSteps)
  have sameQuotient : (EthLib.Consensus.parameters preset a.fork).WHISTLEBLOWER_REWARD_QUOTIENT =
      (parameters preset y.fork).WHISTLEBLOWER_REWARD_QUOTIENT := by
    have yLeast : y.fork ≥ .pectra := Nat.le_trans atLeast atMost
    simp [EthLib.Consensus.parameters, atLeast, yLeast]
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
    (Nat.lt_of_lt_of_le (Finset.mem_range.mp inside) post.registryLifecycle.size_le),
      first, last⟩, ?_⟩
  rw [sameQuotient]
  exact Nat.div_le_div_right (Base.le_foldr_max (List.mem_map_of_mem onPath))
end PinSplit

/-! ## PinEffectiveFloor -/

namespace PinSplit2

open Base Uint64 Models

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- A key's cap at a state, `0` past the registry. -/
private def capAt (z : ForkedBeaconState preset) (i : ℕ) : ℕ :=
  ((z.state.validators.data[i]?).map fun v =>
    (withdrawalMaxEffectiveBalance preset z.fork v).toNat).getD 0

/-- A successful update of the effective balances applies the scalar update at each index.

It reads the balance of the index, which it keeps. -/
private theorem effective_update_at {f : Fork} {s t : BeaconState preset f}
    (ok : processEffectiveBalanceUpdates s = .ok t) {i : ℕ}
    (inside : i < s.validators.data.size) :
    ∃ (v : Validator) (balance new : Gwei), s.validators.data[i]? = some v ∧
      s.balances.data[i]? = some balance ∧
      t.validators.data[i]? = some { v with effectiveBalance := new } ∧
      t.balances = s.balances ∧
      updatedEffectiveBalance preset (withdrawalMaxEffectiveBalance preset f v) balance
        v.effectiveBalance = .ok new := by
  have found : ∃ v, s.validators.data[i]? = some v :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  obtain ⟨v, found⟩ := found
  have owned : ∃ balance, s.balances.data[i]? = some balance := by
    have computed := ok
    unfold processEffectiveBalanceUpdates at computed
    obtain ⟨middle, next, prefixOk, atIndex, -⟩ :=
      (foldlM_ok_steps (fun _ _ => True) (fun _ => trivial) (fun _ _ => trivial)
        (fun _ _ _ _ => trivial) computed).2 i (by simpa using inside)
    have balances : middle.balances = s.balances :=
      foldlM_ok_invariant (fun c : BeaconState preset f => c.balances = s.balances)
        (fun _ _ _ kept step => by
          simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at step
          obtain ⟨_, _, _, _, _, _, set⟩ := step
          obtain ⟨_, rfl⟩ := setValidatorAt_ok set
          exact kept) rfl prefixOk
    simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok, List.getElem_range] at atIndex
    obtain ⟨_, _, balance, read, _⟩ := atIndex
    exact ⟨balance, balances ▸ getBalanceAt_eq_ok_iff.mp read⟩
  obtain ⟨balance, owned⟩ := owned
  obtain ⟨new, read, updated⟩ := processEffectiveBalanceUpdates_effectiveBalance_eq ok found owned
  exact ⟨v, balance, new, found, owned, read, processEffectiveBalanceUpdates_balances ok, updated⟩

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
  obtain ⟨v, balance, new, found, owned, read, -, updated⟩ := effective_update_at ok inside
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
  obtain ⟨v, balance, new, found, owned, read, -, updated⟩ := effective_update_at ok inside
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

open DirectSafety PinSplit

/-! ### One key's reward in an epoch pass -/

/-- The epoch-pass reward credits to the key in one step.

A slot step's events are those of its epoch pass and its upgrades.

So its `.rewards` events are the epoch's rewards.

A block step has none counted: its proposer credits are charged elsewhere. -/
private def epochRewards (v : ℕ) {x y : ForkedBeaconState preset}
    (step : Step config checks x y) : ℕ :=
  match step with
  | .slot ok =>
    ((((Step.slot (config := config) (checks := checks) ok).balanceEvents.toOption.getD []).filter
      (·.source = .rewards)).map (keyCredit v)).sum
  | .block .. => 0

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

/-- The balances at the two ends of a chain of events rise by at most the credits of the events. -/
private theorem chain_credit_le (i : ℕ) :
    ∀ (L : List (BalanceEvent preset)) (a b : ℕ),
    L.IsChain (fun e e' => ∀ j, actualBalanceAt e.after j = actualBalanceAt e'.before j) →
    (∀ e ∈ L.head?, actualBalanceAt e.before i = a) →
    (∀ e ∈ L.getLast?, actualBalanceAt e.after i = b) →
    (L = [] → b = a) → b ≤ a + (L.map (keyCredit i)).sum := by
  intro L
  induction L with
  | nil =>
    intro a b _ _ _ empty
    have same := empty rfl
    simp only [List.map_nil, List.sum_nil]
    omega
  | cons e rest ih =>
    intro a b link head last _
    have first : actualBalanceAt e.before i = a := head e (by simp)
    cases rest with
    | nil =>
      have final : actualBalanceAt e.after i = b := last e (by simp)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, keyCredit]
      omega
    | cons e' rest' =>
      have linked := List.isChain_cons_cons.mp link
      have next := ih (actualBalanceAt e'.before i) b linked.2
        (fun f hf => by
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hf
          subst hf
          rfl)
        (fun f hf => last f (by rw [List.getLast?_cons_cons]; exact hf))
        (fun h => absurd h (List.cons_ne_nil _ _))
      have joined := linked.1 i
      have expand : ((e :: e' :: rest').map (keyCredit i)).sum =
          keyCredit i e + ((e' :: rest').map (keyCredit i)).sum := by simp
      have credit : keyCredit i e = actualBalanceAt e.after i - actualBalanceAt e.before i := rfl
      rw [expand]
      omega

/-- A step raises the balance of a key by at most the credits of its events. -/
private theorem step_balance_le_credits {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (early : y.fork < .glamsterdam)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events) (i : ℕ) :
    actualBalanceAt y i ≤ actualBalanceAt x i + (events.map (keyCredit i)).sum := by
  obtain ⟨p, first, second, -, split, firstEmpty, head1, last1, link1, secondEmpty, head2, last2,
    link2, -⟩ := step.balanceChain early replayed
  subst split
  have one := chain_credit_le i first (actualBalanceAt x i) (actualBalanceAt p i) link1
    (fun e he => head1 e he i) (fun e he => last1 e he i) (fun h => firstEmpty h i)
  have two := chain_credit_le i second (actualBalanceAt p i) (actualBalanceAt y i) link2
    (fun e he => head2 e he i) (fun e he => last2 e he i) (fun h => secondEmpty h i)
  rw [List.map_append, List.sum_append]
  omega

/-- A sum over a list splits over a test and its complement. -/
private theorem sum_filter_split {α : Type} (L : List α) (p : α → Bool) (f : α → ℕ) :
    (L.map f).sum = ((L.filter p).map f).sum + ((L.filter fun a => !p a).map f).sum := by
  induction L with
  | nil => rfl
  | cons a rest ih =>
    by_cases hp : p a = true
    · simp only [List.filter_cons, hp, ↓reduceIte, List.map_cons, List.sum_cons, Bool.not_true,
        Bool.false_eq_true]
      omega
    · have hp' : p a = false := by simpa using hp
      simp only [List.filter_cons, hp', Bool.false_eq_true, ↓reduceIte, List.map_cons,
        List.sum_cons, Bool.not_false]
      omega

/-- A step raises the balance of a key by at most its epoch rewards and its other credits. -/
private theorem step_balance_le {m n : ForkedBeaconState preset} (step : Step config checks m n)
    (early : n.fork < .glamsterdam) (i : ℕ) :
    actualBalanceAt n i ≤ actualBalanceAt m i + epochRewards i step +
      stepCredit (fun _ => true) (fun s => decide (s ≠ .rewards)) i step := by
  obtain ⟨events, ok⟩ := step.balanceEvents_ok early
  have base := step_balance_le_credits step early ok i
  cases step with
  | block engine signed due okb =>
    simp only [epochRewards, stepCredit, ok, Except.toOption, Option.getD_some,
      List.filter_true] at base ⊢
    omega
  | slot oks =>
    simp only [epochRewards, stepCredit, ok, Except.toOption, Option.getD_some] at base ⊢
    have split := sum_filter_split events (fun e => decide (e.source = .rewards)) (keyCredit i)
    have same : (events.filter fun e => !decide (e.source = .rewards)) =
        events.filter fun e => decide (e.source ≠ .rewards) := by
      congr 1
    rw [same] at split
    omega

/-- The bound on a key's balance along a run: its start, the epoch rewards, and its other credits.

The epoch rewards are those of the epochs that the run ends, at the rate given by `E` and `P`. -/
private def creditBound {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (i high E P : ℕ) : ℕ :=
  actualBalanceAt x i +
    ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) *
      (E / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) +
    (creditScan (fun _ => true) (fun s => decide (s ≠ .rewards)) i high tail).1

end Rewards

/-- A balance ceiling, an envelope or a floor on a key's balance bounds its effective balance.

First, suppose a key's balance stays at least `floor` at every state of the run.

Suppose also that its cap stays at least `capLow`.

Then its effective balance at the end is at least the least of three values.

They are its effective balance at the start, `capLow`, and `floor` rounded down to an increment.

Second, suppose the effective balance at the start is a whole number of increments.

Suppose its effective balance stays at most `top`, and its balance near `top`.

Near means within the downward band.

Suppose also that its cap stays at least its effective balance at the start.

Then no downward update fires.

So the effective balance at the end is at least that at the start.

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

Suppose the rate of the rewards at every state is at most `P`, and the run ends by the epoch `high + 1`.

Suppose also that `E` is at least the greatest effective balance that the bound below allows.

Then the balance at every state is at most its start, plus the epoch rewards at the rate of `E`.

It also adds the other credits that the events of the run give the key. -/
private theorem Run.effective_floor_pair {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ x.fork)
    (i : ℕ) (inside : i < x.state.validators.data.size)
    (floor capLow top capHigh high E P : ℕ) :
    ((∀ z ∈ tail.balancePath, floor ≤ actualBalanceAt z i) →
      (∀ z ∈ tail.balancePath, capLow ≤ capAt z i) →
      min (effectiveAt x i)
        (min capLow (floor - floor % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
          effectiveAt y i) ∧
    (effectiveAt x i % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 →
      (∀ z ∈ tail.balancePath, effectiveAt z i ≤ top) →
      (∀ z ∈ tail.balancePath, top ≤ actualBalanceAt z i + preset.downwardBand) →
      (∀ z ∈ tail.balancePath, effectiveAt x i ≤ capAt z i) →
      effectiveAt x i ≤ effectiveAt y i) ∧
    (∀ ceil : ℕ, capHigh % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 →
      effectiveAt x i ≤ capHigh →
      (∀ z ∈ tail.balancePath, min (actualBalanceAt z i) capHigh ≤ ceil) →
      (∀ z ∈ tail.balancePath, capAt z i ≤ capHigh) →
      effectiveAt y i ≤ max (effectiveAt x i)
        (min (ceil - ceil % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) capHigh) ∧
      ((getCurrentEpoch y.state).toNat ≤ (getCurrentEpoch x.state).toNat →
        effectiveAt y i = effectiveAt x i) ∧
      ((getCurrentEpoch x.state).toNat < (getCurrentEpoch y.state).toNat →
        effectiveAt y i ≤ ceil + preset.downwardBand) ∧
      (getCurrentEpoch x.state).toNat ≤ (getCurrentEpoch y.state).toNat) ∧
    (capHigh % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 → effectiveAt x i ≤ capHigh →
      (∀ z ∈ tail.balancePath, capAt z i ≤ capHigh) →
      (∀ z ∈ tail.balancePath, ∀ total perIncrement : Gwei,
        getTotalActiveBalance z.state = .ok total →
        getBaseRewardPerIncrement preset total = .ok perIncrement →
        perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices z.state
          (getPreviousEpoch z.state)).toFinset, effectiveAt z j.toNat) /
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
          P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) →
      (getCurrentEpoch y.state).toNat ≤ high + 1 →
      max (effectiveAt x i) (min capHigh (creditBound tail i high E P -
        creditBound tail i high E P % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ E →
      ∀ z ∈ tail.balancePath, actualBalanceAt z i ≤ creditBound tail i high E P) := by
  induction tail with
  | nil => exact ⟨fun _ _ => Nat.min_le_left _ _, fun _ _ _ _ => Nat.le_refl _,
      fun _ _ _ _ _ => ⟨Nat.le_max_left _ _, fun _ => rfl, fun h => absurd h (Nat.lt_irrefl _),
        Nat.le_refl _⟩,
      fun _ _ _ _ _ _ z hz => by
        rw [Run.balancePath, List.mem_singleton] at hz
        subst hz
        simp [creditBound]⟩
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
        (∀ z ∈ (pre.snoc step).balancePath, capAt z i ≤ capHigh) →
        (∀ z ∈ (pre.snoc step).balancePath, ∀ total perIncrement : Gwei,
          getTotalActiveBalance z.state = .ok total →
          getBaseRewardPerIncrement preset total = .ok perIncrement →
          perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices z.state
            (getPreviousEpoch z.state)).toFinset, effectiveAt z j.toNat) /
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
            P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) →
        (getCurrentEpoch last.state).toNat ≤ high + 1 →
        max (effectiveAt x i) (min capHigh (creditBound (pre.snoc step) i high E P -
          creditBound (pre.snoc step) i high E P % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ E →
        (∀ z ∈ step.balancePath, z = middle ∨ z = last) →
        ∀ z ∈ (pre.snoc step).balancePath,
          actualBalanceAt z i ≤ creditBound (pre.snoc step) i high E P := by
      intro alignedHigh startCap capC rate endEp closed pathCases z hz
      have xm : (getCurrentEpoch x.state).toNat ≤ (getCurrentEpoch middle.state).toNat :=
        UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
      have ml : (getCurrentEpoch middle.state).toNat ≤ (getCurrentEpoch last.state).toNat :=
        UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
      have within : (getCurrentEpoch middle.state).toNat ≤ high + 1 := by omega
      have scan := PinSplit.creditScan_snoc_fst (fun _ => true) (fun s => decide (s ≠ .rewards))
        i high pre step
      simp only [within, ↓reduceIte] at scan
      have tailEq : creditBound (pre.snoc step) i high E P =
          creditBound pre i high E P +
            ((getCurrentEpoch last.state).toNat - (getCurrentEpoch middle.state).toNat) *
              (E / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum /
                WEIGHT_DENOMINATOR.toNat) +
            PinSplit.stepCredit (fun _ => true) (fun s => decide (s ≠ .rewards)) i step := by
        unfold creditBound
        rw [scan]
        generalize E / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum /
          WEIGHT_DENOMINATOR.toNat = G
        have split : ((getCurrentEpoch last.state).toNat - (getCurrentEpoch x.state).toNat) * G =
            ((getCurrentEpoch middle.state).toNat - (getCurrentEpoch x.state).toNat) * G +
              ((getCurrentEpoch last.state).toNat - (getCurrentEpoch middle.state).toNat) * G := by
          rw [← Nat.add_mul]
          congr 1
          omega
        rw [split]
        omega
      have closedPre : max (effectiveAt x i) (min capHigh (creditBound pre i high E P -
          creditBound pre i high E P % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ E :=
        le_trans (max_le_max le_rfl (min_le_min le_rfl (rounded_mono _ (by omega)))) closed
      have ihPre := ihCredit alignedHigh startCap
        (fun p member => capC p (List.mem_append_left _ member))
        (fun p member => rate p (List.mem_append_left _ member)) within closedPre
      rcases List.mem_append.mp hz with old | stepMember
      · exact (ihPre z old).trans (by omega)
      · rcases pathCases z stepMember with rfl | rfl
        · exact (ihPre _ atMiddle).trans (by omega)
        · have ceilings : ∀ p ∈ pre.balancePath,
              min (actualBalanceAt p i) capHigh ≤ creditBound (pre.snoc step) i high E P :=
            fun p member => (Nat.min_le_left _ _).trans ((ihPre p member).trans (by omega))
          obtain ⟨c1, -, -, -⟩ := ihCeiling (creditBound (pre.snoc step) i high E P) alignedHigh startCap
            ceilings
            (fun p member => capC p (List.mem_append_left _ member))
          rw [Nat.min_comm] at c1
          have envelope : effectiveAt middle i ≤ E := c1.trans closed
          have rewards := epochRewards_le step altair early i room E P envelope
            (rate middle (List.mem_append_left _ atMiddle))
          have stepBound := step_balance_le step early i
          have mid := ihPre _ atMiddle
          rw [tailEq]
          omega
    cases step with
    | @block fork before after engine signed due ok =>
      have kept := effectiveKept_processBlock (applySignedBlock_ok ok).2.1 i room
      have epoch : (getCurrentEpoch after).toNat = (getCurrentEpoch before).toNat := by
        simp only [getCurrentEpoch, processBlock_slot (applySignedBlock_ok ok).2.1]
      refine ⟨fun balanceFloor capFloor => ?_, fun aligned envelope near capFloor => ?_,
        fun ceil alignedHigh startCap balanceCeil capCeil => ?_,
        fun alignedHigh startCap capC rate endEp closed =>
          key alignedHigh startCap capC rate endEp closed
            (fun z hz => by simpa [Step.balancePath] using hz)⟩
      · rw [kept]
        exact ihFloor (fun p member => balanceFloor p (List.mem_append_left _ member))
          (fun p member => capFloor p (List.mem_append_left _ member))
      · rw [kept]
        exact ihEnvelope aligned (fun p member => envelope p (List.mem_append_left _ member))
          (fun p member => near p (List.mem_append_left _ member))
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
      refine ⟨fun balanceFloor capFloor => ?_, fun aligned envelope near capFloor => ?_,
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
          (fun v read => by simpa [capAt, read] using capped)
        exact (Nat.min_le_right _ _).trans ((Nat.min_le_right _ _).trans (rounded_mono _ funded))
      · have nearNext := near _ (List.mem_append_right _ onPath)
        have capped := capFloor _ (List.mem_append_right _ onPath)
        have prior := ihEnvelope aligned
          (fun p member => envelope p (List.mem_append_left _ member))
          (fun p member => near p (List.mem_append_left _ member))
          (fun p member => capFloor p (List.mem_append_left _ member))
        have atTop := envelope _ (List.mem_append_left _ atMiddle)
        refine effective_floor_slot advanced i (capAt ⟨middle.fork, next⟩ i) _ room capped
          (fun fires => ?_) prior (fun v read => by simp [capAt, read])
        have eta : effectiveAt (⟨middle.fork, middle.state⟩ : ForkedBeaconState preset) i =
            effectiveAt middle i := rfl
        rw [eta] at fires
        rcases fires with below | above
        · omega
        · have lift := rounded_mono preset.EFFECTIVE_BALANCE_INCREMENT.toNat
            (show effectiveAt x i ≤ actualBalanceAt ⟨middle.fork, next⟩ i by omega)
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
          funded (fun v read => by simpa [capAt, read] using capped)
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
private theorem Run.effective_floor_rounded {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ x.fork)
    (i : ℕ) (inside : i < x.state.validators.data.size) (floor capLow : ℕ)
    (balanceFloor : ∀ z ∈ tail.balancePath, floor ≤ actualBalanceAt z i)
    (capFloor : ∀ z ∈ tail.balancePath, capLow ≤ capAt z i) :
    min (effectiveAt x i) (min capLow (floor - floor % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
      effectiveAt y i :=
  (Run.effective_floor_pair tail early fulu i inside floor capLow 0 0 0 0 0).1 balanceFloor
    capFloor

/-- H4. A balance floor and a cap floor along a run give an effective-balance floor.

Suppose a key's balance stays at least `floor` at every state of a run.

Suppose also that its cap stays at least `capLow`.

Then its effective balance at the end is at least the least of three values.

They are its effective balance at the start, `capLow`, and `floor` less one increment of rounding.

This follows from `Run.effective_floor_rounded`.

The floor rounded down to an increment is at least `floor + 1 - inc`. -/
private theorem Run.effective_floor_of_balance_floor {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ x.fork)
    (bands : preset.IncrementWithinUpwardBand) (i : ℕ) (inside : i < x.state.validators.data.size)
    (floor capLow : ℕ)
    (balanceFloor : ∀ z ∈ tail.balancePath, floor ≤ actualBalanceAt z i)
    (capFloor : ∀ z ∈ tail.balancePath, capLow ≤ capAt z i) :
    min (effectiveAt x i) (min capLow (floor + 1 - preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
      effectiveAt y i := by
  have remainder := Nat.mod_lt floor bands.1
  refine Nat.le_trans ?_
    (Run.effective_floor_rounded tail early fulu i inside floor capLow balanceFloor capFloor)
  omega

/-- An envelope on the effective balance, and a balance near it, stop it from falling.

Suppose a key's effective balance stays at most `top` at every state of a run.

Suppose also that its balance stays within the downward band of `top`.

And that its cap stays at least its effective balance at the start.

Then no downward update fires.

So its effective balance at the end is at least that at the start.

The effective balance at the start must be a whole number of increments. -/
private theorem Run.effective_floor_of_envelope {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ x.fork)
    (i : ℕ) (inside : i < x.state.validators.data.size) (top : ℕ)
    (aligned : effectiveAt x i % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (envelope : ∀ z ∈ tail.balancePath, effectiveAt z i ≤ top)
    (near : ∀ z ∈ tail.balancePath, top ≤ actualBalanceAt z i + preset.downwardBand)
    (capFloor : ∀ z ∈ tail.balancePath, effectiveAt x i ≤ capAt z i) :
    effectiveAt x i ≤ effectiveAt y i :=
  (Run.effective_floor_pair tail early fulu i inside 0 0 top 0 0 0 0).2.1 aligned envelope near
    capFloor

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
private theorem Run.effective_ceiling_of_balance_ceiling {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ x.fork)
    (i : ℕ) (inside : i < x.state.validators.data.size) (ceil capHigh : ℕ)
    (alignedHigh : capHigh % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (startCap : effectiveAt x i ≤ capHigh)
    (balanceCeil : ∀ z ∈ tail.balancePath, min (actualBalanceAt z i) capHigh ≤ ceil)
    (capCeil : ∀ z ∈ tail.balancePath, capAt z i ≤ capHigh) :
    effectiveAt y i ≤ max (effectiveAt x i)
      (min (ceil - ceil % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) capHigh) ∧
    ((getCurrentEpoch y.state).toNat ≤ (getCurrentEpoch x.state).toNat →
      effectiveAt y i = effectiveAt x i) ∧
    ((getCurrentEpoch x.state).toNat < (getCurrentEpoch y.state).toNat →
      effectiveAt y i ≤ ceil + preset.downwardBand) ∧
    (getCurrentEpoch x.state).toNat ≤ (getCurrentEpoch y.state).toNat :=
  (Run.effective_floor_pair tail early fulu i inside 0 0 0 capHigh 0 0 0).2.2.1 ceil
    alignedHigh startCap balanceCeil capCeil

end PinSplit2

end GroupB

section GroupD

/-! ## PinPenaltyRate -/

namespace PinSplit2

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

The floor of a quotient that is at least one is at least half of it.

The left side is `passPenaltyRate config z v` of this file, restated. -/
private theorem passPenaltyRate_le_leak (z : ForkedBeaconState preset) (v : ℕ) (pulledTotal : ℕ)
    (scoreBound : ℕ)
    (size : 10 ^ 8 ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (roomy : 2 ^ 33 ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat)
    (pulledFits : pulledTotal < 2 ^ 64)
    (aligned : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ effectiveAt z v)
    (band : 2 * pulledTotal ≤ 3 * max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      (∑ i ∈ (Finset.range z.state.validators.data.size).filter
          (fun i => isActiveAt z.state (getCurrentEpoch z.state) i = true),
        ((z.state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0))
    (scored : (if altair : .altair ≤ z.fork then
        (((z.state.inactivityScores altair).data[v]?).map (·.toNat)).getD 0 else 0) +
      config.INACTIVITY_SCORE_BIAS.toNat ≤ scoreBound) :
    let inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    let total := max inc
      (∑ i ∈ (Finset.range z.state.validators.data.size).filter
          (fun i => isActiveAt z.state (getCurrentEpoch z.state) i = true),
        ((z.state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0)
    let score := if altair : .altair ≤ z.fork then
        (((z.state.inactivityScores altair).data[v]?).map (·.toNat)).getD 0 else 0
    let quarter := if 18 * inc ≤ pulledTotal then pulledTotal / 4 else inc / 5
    let perIncrement := inc * preset.BASE_REWARD_FACTOR.toNat / quarter.sqrt
    (TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat) * preset.BASE_REWARD_FACTOR.toNat *
        effectiveAt z v / (WEIGHT_DENOMINATOR.toNat * total.sqrt) +
      effectiveAt z v * (score + config.INACTIVITY_SCORE_BIAS.toNat) /
        (config.INACTIVITY_SCORE_BIAS.toNat *
          (parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat) ≤
    2 * (effectiveAt z v / inc * perIncrement) +
      effectiveAt z v * scoreBound /
        (config.INACTIVITY_SCORE_BIAS.toNat *
          (parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat) := by
  intro inc total score quarter perIncrement
  have sizeInc : 10 ^ 8 ≤ inc := size
  have positive : 0 < inc := by omega
  have weights : TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat = 40 := by decide
  have denominator : WEIGHT_DENOMINATOR.toNat = 64 := by decide
  rw [weights, denominator]
  obtain ⟨k, hk⟩ := aligned
  have hinc : inc ≤ total := le_max_left _ _
  have hfactor : 1 ≤ preset.BASE_REWARD_FACTOR.toNat := by
    rcases Nat.eq_zero_or_pos preset.BASE_REWARD_FACTOR.toNat with zero | pos
    · rw [zero, Nat.mul_zero] at roomy
      exact absurd roomy (by decide)
    · exact pos
  -- the numerator of the per-increment reward, `X`, dominates the square root of the quarter
  obtain ⟨X, hX⟩ : ∃ X, inc * preset.BASE_REWARD_FACTOR.toNat = X := ⟨_, rfl⟩
  rw [hX] at roomy
  have hp : perIncrement = X / quarter.sqrt := by
    simp only [perIncrement, hX]
  have incX : inc ≤ X := by
    rw [← hX]
    exact Nat.le_mul_of_pos_right _ hfactor
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

/-- `roomy` on mainnet and minimal. -/
private theorem roomy_mainnet :
    2 ^ 33 ≤ Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT.toNat *
      Preset.mainnet.BASE_REWARD_FACTOR.toNat ∧
    2 ^ 33 ≤ Preset.minimal.EFFECTIVE_BALANCE_INCREMENT.toNat *
      Preset.minimal.BASE_REWARD_FACTOR.toNat := by
  decide
end PinSplit2

/-! ## PinWithdrawalFloor -/

namespace PinSplit3

open Base Uint64 Models

variable {preset : Preset} {fork : Fork}

/-- The loop of the queued partial withdrawals keeps a floor of a key's balance.

What the withdrawals take from the key, plus a floor, stays within its balance.

The floor is at most the activation balance.

Each entry pays at most the balance left above the activation balance. -/
private theorem getPendingPartialWithdrawals_loop_floor {state : BeaconState preset fork}
    {prior : Array Withdrawal} {epoch : Epoch} {limit : Nat} {index : ValidatorIndex}
    {balance : Gwei} {floor : Nat}
    (found : state.balances.data[index.toNat]? = some balance)
    (capped : floor ≤ preset.MIN_ACTIVATION_BALANCE.toNat) :
    ∀ (queue : List PendingPartialWithdrawal) (withdrawals : Array Withdrawal)
      (next : WithdrawalIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    withdrawnFrom (prior ++ withdrawals) index + floor ≤ balance.toNat →
    getPendingPartialWithdrawals.loop state prior epoch limit queue withdrawals next processed =
      .ok result →
    withdrawnFrom (prior ++ result.1) index + floor ≤ balance.toNat
  | [], _, _, _, _, bounded, computed => by
    simp only [getPendingPartialWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact bounded
  | pending :: rest, _, _, _, _, bounded, computed => by
    simp only [getPendingPartialWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact bounded
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, left, leftOk, computed⟩ := computed
      have leftOk := liftAccessor_ok.mp leftOk
      split at computed
      · rename_i eligible
        simp only [isEligibleForPartialWithdrawals, Bool.and_eq_true, decide_eq_true_eq]
          at eligible
        simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨⟨appended, following⟩, appendedOk, rest'⟩ := computed
        refine getPendingPartialWithdrawals_loop_floor found capped rest _ _ _ ?_ rest'
        rw [appendWithdrawal_withdrawnFrom_eq appendedOk]
        split
        · rename_i named
          subst named
          obtain ⟨read, readAt, sum⟩ := getBalanceAfterWithdrawals_ok leftOk
          rw [found, Option.some.injEq] at readAt
          subst readAt
          have above := UInt64.lt_iff_toNat_lt.mp eligible.2
          have paid : (min (left - preset.MIN_ACTIVATION_BALANCE) pending.amount).toNat ≤
              left.toNat - preset.MIN_ACTIVATION_BALANCE.toNat := by
            have := UInt64.toNat_sub_of_le left preset.MIN_ACTIVATION_BALANCE
              (UInt64.le_of_lt eligible.2)
            rw [UInt64.min_def]
            split
            · omega
            · have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp ‹_›)
              omega
          omega
        · simpa using bounded
      · exact getPendingPartialWithdrawals_loop_floor found capped rest _ _ _ bounded computed

/-- From Electra and before Gloas, a block's withdrawals leave a key that is not yet withdrawable.

It keeps at least the least of its balance before and `MIN_ACTIVATION_BALANCE`.

A pending partial pays at most the balance above `MIN_ACTIVATION_BALANCE`.

The sweep pays at most the balance above the key's cap.

That cap is at least `MIN_ACTIVATION_BALANCE`, because `compounding` bounds a compounding cap.

Only a withdrawable key is paid in full. -/
private theorem processWithdrawals_balance_floor {state after : BeaconState preset fork}
    (capella : .shapella ≤ fork) (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after)
    (i : Nat) (v : Validator) (found : state.validators.data[i]? = some v)
    (notWithdrawable : getCurrentEpoch state < v.withdrawableEpoch) :
    min (((state.balances.data[i]?).map (·.toNat)).getD 0) preset.MIN_ACTIVATION_BALANCE.toNat ≤
      ((after.balances.data[i]?).map (·.toNat)).getD 0 := by
  obtain ⟨expected, expectedOk, -, appliedOk⟩ := processWithdrawals_expected early computed
  obtain ⟨applied, appliedFold, balances, -⟩ := applyExpectedWithdrawals_balances appliedOk
  unfold applyWithdrawals at appliedFold
  rw [← Array.foldlM_toList] at appliedFold
  rw [balances]
  cases held : state.balances.data[i]? with
  | none => simp
  | some balance =>
    simp only [Option.map_some, Option.getD_some]
    by_cases small : i < 2 ^ 64
    · have same : i.toUInt64.toNat = i := UInt64.toNat_ofNat_of_lt' small
      rw [← same] at found held
      have bounded := getExpectedWithdrawals_withdrawnFrom (.inl early) expectedOk held
      have lowered := applyWithdrawals_balance (.inl early) _ _ _ _ appliedFold held
        (by simpa using bounded)
      -- the cap of the key is at least the activation balance
      have cap : preset.MIN_ACTIVATION_BALANCE.toNat ≤
          (withdrawalMaxEffectiveBalance preset fork v).toNat := by
        unfold withdrawalMaxEffectiveBalance getMaxEffectiveBalance
        simp only [electra, ↓reduceIte]
        split
        · exact UInt64.le_iff_toNat_le.mp compounding
        · exact Nat.le_refl _
      obtain ⟨partials, next, partialsOk, sweepFloor⟩ :=
        getExpectedWithdrawals_sweep_floor early expectedOk found notWithdrawable held
      simp only [electra, ↓reduceDIte] at partialsOk
      have partialFloor : withdrawnFrom partials i.toUInt64 +
          min balance.toNat preset.MIN_ACTIVATION_BALANCE.toNat ≤ balance.toNat := by
        unfold getPendingPartialWithdrawals at partialsOk
        simp only [bind_ok_iff, ensure_ok_iff] at partialsOk
        obtain ⟨_, _, _, _, loopOk⟩ := partialsOk
        simpa using getPendingPartialWithdrawals_loop_floor held (Nat.min_le_right _ _) _ _ _ _
          (by
            have : withdrawnFrom (#[] ++ #[]) i.toUInt64 = 0 := by simp [withdrawnFrom]
            omega) loopOk
      rw [same] at lowered
      simp only [Array.toArray_toList] at lowered
      cases atLater : applied.balances.data[i]? with
      | none => simp [atLater] at lowered
      | some later =>
        simp only [atLater, Option.map_some, Option.some.injEq] at lowered
        simp only [Option.map_some, Option.getD_some]
        omega
    · -- No withdrawal names the index, so the balance is unchanged.
      have unchanged := applyWithdrawals_unnamed (index := i) _ _ _ appliedFold
        fun withdrawal _ atIndex => by
          have := UInt64.toNat_lt_size withdrawal.validatorIndex
          simp only [UInt64.size] at this
          omega
      rw [unchanged, held]
      simp only [Option.map_some, Option.getD_some]
      exact Nat.min_le_left _ _
end PinSplit3

/-! ## PinEventsKept -/

namespace PinSplit4

open Base Uint64 Models DirectSafety

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- What a chain of steps keeps of the registry, at any forks.

Assigned exits stay, and a slash stays.

The withdrawable epoch of a key with an exit set only rises, and only for a slashed key. -/
private structure Kept {f g : Fork} (s : BeaconState preset f) (t : BeaconState preset g) :
    Prop where
  life : RegistryLifecycle s t
  slashed : SlashedPersistence s t
  withdrawable : WithdrawableKept s t

/-- Two steps keep what one keeps.

The exit of the first comes from its lifecycle, and the slash of the second from its persistence. -/
private theorem Kept.trans {f g h : Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    {u : BeaconState preset h} (one : Kept s t) (two : Kept t u) : Kept s u where
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
private theorem Kept.of_data {f g : Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    (same : t.validators.data = s.validators.data) : Kept s t where
  life := .of_data same
  slashed := .of_data same
  withdrawable i v w found read _ := by
    rw [same, found, Option.some.injEq] at read
    subst read
    exact ⟨UInt64.le_refl _, .inr rfl⟩

/-- A step that keeps the lifecycle, the slashes and each withdrawable epoch keeps everything. -/
private theorem Kept.of_withdrawable {f g : Fork} {s : BeaconState preset f}
    {t : BeaconState preset g} (life : RegistryLifecycle s t) (slashed : SlashedPersistence s t)
    (same : ∀ (i : ℕ) (v : Validator), s.validators.data[i]? = some v →
      ∃ w, t.validators.data[i]? = some w ∧ w.withdrawableEpoch = v.withdrawableEpoch) :
    Kept s t where
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
    (electra : .pectra ≤ fork) (edge : EpochStage.Edge config checks k s t) : Kept s t := by
  cases k
  case registry =>
    simp only [EpochStage.Edge] at edge
    exact ⟨registryLifecycle_processRegistryUpdates edge,
      .of_frame (frame_processRegistryUpdates edge).toFrame,
      withdrawableKept_processRegistryUpdates electra edge⟩
  case pendingDeposits =>
    simp only [EpochStage.Edge, electra, ↓reduceDIte] at edge
    exact Kept.of_withdrawable (registryLifecycle_processPendingDeposits edge)
      (.of_frame (frame_processPendingDeposits edge).toFrame)
      fun i v found => ⟨v, pendingDeposits_entries edge i v found, rfl⟩
  case effectiveBalances =>
    simp only [EpochStage.Edge] at edge
    exact Kept.of_withdrawable (registryLifecycle_processEffectiveBalanceUpdates edge)
      (.of_frame (frame_processEffectiveBalanceUpdates edge).toFrame)
      (effectiveUpdates_withdrawable edge)
  all_goals exact Kept.of_data (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩))

/-- From Electra, a whole epoch transition keeps the registry. -/
private theorem kept_processEpoch {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (ok : processEpoch config checks s = .ok t) : Kept s t :=
  (processEpoch_trace ok).transport (fun a b => Kept a b) (fun _ => Kept.of_data rfl)
    (fun one two => one.trans two)
    (fun _ _ _ _ computed => kept_stage electra (EpochStage.action_cases.mp computed))

/-- From Electra, an upgrade keeps the validators as the same sequence. -/
private theorem upgradeNext_validators {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (electra : .pectra ≤ pre.fork) (computed : upgradeNext config checks pre = .ok post) :
    post.val.state.validators.data = pre.state.validators.data := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
  all_goals try (dsimp only at electra; exact absurd electra (by decide))
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact (upgradeToFulu_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact (upgradeToGloas_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact (upgradeHezeFields_lists _).1

/-- From Electra, a slot of a run keeps the registry. -/
private theorem kept_slot {u w : ForkedBeaconState preset} (electra : .pectra ≤ u.fork)
    (ok : advanceSlotAcross config checks u = .ok w) : Kept u.state w.state := by
  obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
  obtain ⟨_, cached, epoched, _, cachedOk, epochedOk, afterEq⟩ := advanceSlot_ok slotOk
  have cachedKept : Kept u.state cached := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact Kept.of_data rfl
  have epochKept : Kept cached epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact kept_processEpoch electra epochedOk
    · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
      exact epochedOk ▸ Kept.of_data rfl
  have advancedKept : Kept u.state advanced := by
    rw [afterEq]
    exact cachedKept.trans (epochKept.trans (Kept.of_data rfl))
  exact (processUpgrades_induction (forked := ⟨u.fork, advanced⟩)
    (property := fun z => .pectra ≤ z.fork ∧ Kept u.state z.state)
    (fun {_ post} held more => ⟨Nat.le_trans held.1 (Nat.le_of_lt post.property),
      held.2.trans (Kept.of_data (upgradeNext_validators held.1 more))⟩)
    ⟨electra, advancedKept⟩ upgrades).2

/-- From Fulu and before Gloas, a block keeps the registry. -/
private theorem kept_block {fork : Fork} {a t : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    {due : upgradeDue config ⟨fork, a⟩ = false}
    {ok : applySignedBlock config checks engine a signed true = .ok t}
    (fulu : .fusaka ≤ fork) (early : fork < .glamsterdam) (matched : BalancesMatch a) :
    Kept a t := by
  have processed := (applySignedBlock_ok ok).2.1
  have frame := frame_processBlock processed
  refine ⟨registryLifecycle_processBlock processed, .of_frame frame, ?_⟩
  exact Run.withdrawableKept_of_same_epoch (Run.nil.snoc (Step.block engine signed due ok)) early
    fulu (by simp only [getCurrentEpoch, frame.slot]) matched

/-- From Fulu and before Gloas, a run keeps the registry. -/
private theorem kept_run {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (fulu : .fusaka ≤ x.fork) (tail : Run config checks x y) (early : y.fork < .glamsterdam) :
    Kept x.state y.state := by
  induction tail with
  | nil => exact Kept.of_data rfl
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
  kept : Kept p.1 q.1
  slot : q.1.slot = p.1.slot
  events : ∀ e ∈ q.2, e ∈ p.2 ∨ e.source ≠ .deposits

private theorem Grew.refl {f : Fork} (p : BalanceReplay preset f) : Grew p p :=
  ⟨Kept.of_data rfl, rfl, fun _ member => .inl member⟩

private theorem Grew.trans {f : Fork} {p q r : BalanceReplay preset f} (one : Grew p q)
    (two : Grew q r) : Grew p r where
  kept := one.kept.trans two.kept
  slot := two.slot.trans one.slot
  events e member := by
    rcases two.events e member with old | other
    · exact one.events e old
    · exact .inr other

/-- A recorded pass appends one event of its source to the events, after its action. -/
private theorem recordBalance_cases {f : Fork} {source : BalanceSource}
    {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    {p q : BalanceReplay preset f} (ok : recordBalance source limits action p = .ok q) :
    action p.1 = .ok q.1 ∧ ∀ e ∈ q.2, e ∈ p.2 ∨ e.source = source := by
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨⟨credit, debit⟩, _, after, computed, rfl⟩ := ok
  refine ⟨computed, fun e member => ?_⟩
  rcases List.mem_append.mp member with old | added
  · exact .inl old
  · exact .inr (by rw [List.mem_singleton.mp added])

/-- A carried pass changes the state by its action and records nothing. -/
private theorem carryBalance_cases {f : Fork}
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
  obtain ⟨raisedAction, raisedEvents⟩ := recordBalance_cases raisedOk
  obtain ⟨loweredAction, loweredEvents⟩ := recordBalance_cases loweredOk
  have raisedAction := liftAccessor_ok.mp raisedAction
  have loweredAction := liftAccessor_ok.mp loweredAction
  have first : Grew r raised :=
    ⟨Kept.of_data (congrArg (·.data) (increaseBalance_validators raisedAction)),
      (frame_increaseBalance raisedAction).toFrame.slot, fun e member => by
        rcases raisedEvents e member with old | new
        · exact .inl old
        · exact .inr (by rw [new]; decide)⟩
  have second : Grew raised r' :=
    ⟨Kept.of_data (congrArg (·.data) (decreaseBalance_validators loweredAction)),
      (frame_decreaseBalance loweredAction).toFrame.slot, fun e member => by
        rcases loweredEvents e member with old | new
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
  have ofEdge (edge : EpochStage.Edge config checks k p.1 q.1) (same : q.2 = p.2) : Grew p q :=
    ⟨kept_stage electra edge, edge.slot_eq, fun e member => .inl (same ▸ member)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [epochReplayAction] at ok
    obtain ⟨action, same⟩ := carryBalance_cases ok
    exact ofEdge action same
  · simp only [epochReplayAction] at ok
    split at ok
    · obtain ⟨action, same⟩ := carryBalance_cases ok
      rename_i h
      exact ofEdge (by simp only [EpochStage.Edge, h, ↓reduceDIte]; exact action) same
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      subst ok
      exact Grew.refl _
  · simp only [epochReplayAction] at ok
    exact replayRewards_grew ok
  · simp only [epochReplayAction] at ok
    obtain ⟨action, same⟩ := carryBalance_cases ok
    exact ofEdge action same
  · simp only [epochReplayAction] at ok
    obtain ⟨action, events⟩ := recordBalance_cases ok
    have edge : EpochStage.Edge config checks .slashings p.1 q.1 := action
    exact ⟨kept_stage electra edge, edge.slot_eq, fun e member => by
        rcases events e member with old | new
        · exact .inl old
        · exact .inr (by rw [new]; decide)⟩
  · simp only [epochReplayAction] at ok
    split at ok
    · obtain ⟨action, same⟩ := carryBalance_cases ok
      rename_i h
      exact ofEdge (by simp only [EpochStage.Edge, h, ↓reduceDIte]; exact action) same
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      subst ok
      exact Grew.refl _

/-- Every deposit event of a slot step of the run starts at a state that keeps the registry.

A slot step records a deposit event only for the pending deposits of its epoch pass.

So the event starts at the input of that pass.

That input is the state after the first six stages of the epoch.

They are justification, inactivity, rewards, registry updates, slashings and the eth1 reset.

The steps of the run before the slot keep the registry, and so does each of those stages.

Block deposits are not covered.

From Electra they credit no existing key. -/
private theorem Run.events_kept {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (fulu : .fusaka ≤ x.fork) (early : y.fork < .glamsterdam)
    {u w : ForkedBeaconState preset} (ok : advanceSlotAcross config checks u = .ok w)
    (contained : tail.Contains (Step.slot ok))
    {events : List (BalanceEvent preset)}
    (replayed : (Step.slot ok : Step config checks u w).balanceEvents = .ok events) :
    ∀ e ∈ events, e.source = .deposits →
      RegistryLifecycle x.state e.before.state ∧
      WithdrawableKept x.state e.before.state ∧
      getCurrentEpoch e.before.state ≤ getCurrentEpoch y.state := by
  intro e member source
  obtain ⟨pre, post, rfl⟩ := Run.contains_split tail (Step.slot ok) contained
  have stepFork := (Step.slot ok : Step config checks u w).chainStep.fork_le
  have earlyW : w.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early
  have earlyU : u.fork < .glamsterdam := Nat.lt_of_le_of_lt stepFork earlyW
  have fuluU : .fusaka ≤ u.fork := Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps)
  have electraU : .pectra ≤ u.fork := Nat.le_trans (by decide) fuluU
  have run : Kept x.state u.state := kept_run shared genesis fulu pre earlyU
  have epochLe : getCurrentEpoch u.state ≤ getCurrentEpoch y.state :=
    currentEpoch_le_of_chainSteps
      (Relation.ReflTransGen.head (Step.slot ok : Step config checks u w).chainStep
        post.chainSteps)
  obtain ⟨advanced, cached, crossings, advanceOk, upgrades, cachedOk, crossingOk, branch⟩ :=
    Step.balanceEvents_slot ok earlyW replayed
  have noCrossings : crossings = [] :=
    DirectSafety.Apriori.Internal.upgradeBalanceReplay_electra_nil
      (u := ⟨u.fork, advanced⟩) electraU crossingOk
  rcases branch with ⟨_, eventsEq⟩ | ⟨middle, updated, recorded, recordOk, _, _, _, eventsEq, _⟩
  · rw [eventsEq, noCrossings] at member
    cases member
  rw [eventsEq, noCrossings, List.append_nil] at member
  have cachedKept : Kept u.state cached := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact Kept.of_data rfl
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
      obtain ⟨deposited, _, rfl⟩ := first
      obtain ⟨consolidated, _, same⟩ := second
      simp only [Prod.mk.injEq] at same
      obtain ⟨-, rfl⟩ := same
      rcases List.mem_append.mp member with old | last
      · rcases List.mem_append.mp old with old | added
        · rcases grew.events e old with listed | other
          · cases listed
          · exact absurd source other
        · rw [List.mem_singleton.mp added]
          have total : Kept x.state six.1 := run.trans (cachedKept.trans grew.kept)
          refine ⟨total.life, total.withdrawable, ?_⟩
          have same : getCurrentEpoch six.1 = getCurrentEpoch u.state := by
            simp only [getCurrentEpoch, grew.slot, cachedSlot]
          exact same ▸ epochLe
      · rw [List.mem_singleton.mp last] at source
        cases source
end PinSplit4

end GroupD

section GroupA

/-! ## PinExitCredits -/

namespace PinSplit

open Base Uint64 Models DirectSafety

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-! ## Deposits leave the balance of an exiting key alone -/

/-- Every exiting key of the first state keeps its balance in the second state. -/
private def KeepsExiting {f g : Fork} (s : BeaconState preset f) (t : BeaconState preset g) :
    Prop :=
  ∀ (i : ℕ) (v : Validator), s.validators.data[i]? = some v → v.exitEpoch.toNat < 2 ^ 64 - 1 →
    (getCurrentEpoch s).toNat < v.withdrawableEpoch.toNat →
    t.balances.data[i]? = s.balances.data[i]?

/-- Every deposit event of the list leaves the balance of an exiting key alone. -/
private def Quiet (events : List (BalanceEvent preset)) : Prop :=
  ∀ e ∈ events, e.source = .deposits → KeepsExiting e.before.state e.after.state

/-- The event raises no balance of the registry. -/
private def Unconditional (e : BalanceEvent preset) : Prop :=
  ∀ i, actualBalanceAt e.after i ≤ actualBalanceAt e.before i

private theorem quiet_nil : Quiet ([] : List (BalanceEvent preset)) := fun _ mem => by
  simp at mem

private theorem quiet_carry {f : Fork}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    {pre post : BalanceReplay preset f} (initial : Quiet pre.2)
    (ok : carryBalance action pre = .ok post) : Quiet post.2 := by
  simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  exact initial

private theorem quiet_record {f : Fork} {source : BalanceSource}
    {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    {pre post : BalanceReplay preset f} (initial : Quiet pre.2)
    (keeps : source = .deposits → ∀ t, action pre.1 = .ok t → KeepsExiting pre.1 t)
    (ok : recordBalance source limits action pre = .ok post) : Quiet post.2 := by
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨⟨credit, debit⟩, _, t, actionOk, rfl⟩ := ok
  intro e member sourceEq
  rcases List.mem_append.mp member with old | new
  · exact initial e old sourceEq
  · obtain rfl := List.mem_singleton.mp new
    exact keeps sourceEq t actionOk

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
    simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, rfl⟩ := ok
    exact initial
  have record {pre post : BalanceReplay preset f} {source : BalanceSource}
      {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
      {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
      (notDeposit : source ≠ .deposits) (notConsolidation : source ≠ .consolidations)
      (initial : P pre.2) (ok : recordBalance source limits action pre = .ok post) :
      P post.2 := by
    simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨⟨credit, debit⟩, _, t, _, rfl⟩ := ok
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
      simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨⟨credit, debit⟩, _, t, actionOk, rfl⟩ := ok
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
    ∀ e ∈ post.2, e.source = .deposits → Unconditional e :=
  blockReplay_invariant electra early (fun l => ∀ e ∈ l, e.source = .deposits → Unconditional e)
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
private def Located {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (e : BalanceEvent preset) : Prop :=
  Unconditional e ∨ ∃ (u w : ForkedBeaconState preset)
    (ok : advanceSlotAcross config checks u = .ok w) (es : List (BalanceEvent preset)),
    tail.Contains (Step.slot ok) ∧ (Step.slot ok : Step config checks u w).balanceEvents = .ok es ∧
      e ∈ es ∧ KeepsExiting e.before.state e.after.state

/-- Locate each deposit event of a run. -/
private theorem run_located {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    ∀ e ∈ events, e.source = .deposits → Located tail e := by
  induction tail generalizing events with
  | nil => cases replayed; intro e member; simp at member
  | @snoc middle last pre step ih =>
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    have priorLocated := ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early) priorOk
    have lift : ∀ e, Located pre e → Located (pre.snoc step) e := by
      rintro e (unconditional | ⟨u, w, ok, es, contains, replayedEs, member, keeps⟩)
      · exact .inl unconditional
      · exact .inr ⟨u, w, ok, es, .earlier contains step, replayedEs, member, keeps⟩
    by_cases selected : (getCurrentEpoch middle.state).toNat ≤ high + 1
    · simp only [selected, ↓reduceIte, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at rest
      obtain ⟨added, addedOk, rfl⟩ := rest
      have inFork : .pectra ≤ middle.fork :=
        Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
      intro e member sourceEq
      rcases List.mem_append.mp member with old | new
      · exact lift e (priorLocated e old sourceEq)
      · cases step with
        | block engine signed due ok =>
          exact .inl (blockReplay_unconditional inFork early engine _ _
            (Step.balanceEvents_block early addedOk) e new sourceEq)
        | slot ok =>
          exact .inr ⟨_, _, ok, added, .last pre _, addedOk, new,
            slot_quiet ok early addedOk e new sourceEq⟩
    · simp only [selected, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      intro e member sourceEq
      exact lift e (priorLocated e member sourceEq)

/-! ## Consolidation credits of one pass -/

/-- The stake that a pending consolidation can move at a pass: the source's effective balance.

It counts only a source that is unslashed and can withdraw by the next epoch.

A pass reads the other sources without moving anything. -/
private def sourceBound {f : Fork} (s : BeaconState preset f) (next : Epoch)
    (c : PendingConsolidation) : ℕ :=
  match s.validators.data[c.sourceIndex.toNat]? with
  | some v => if v.slashed = false ∧ v.withdrawableEpoch ≤ next then v.effectiveBalance.toNat else 0
  | none => 0

/-- The credits of some events are within the credits of their keys below a bound on the sizes. -/
private theorem credits_sum_le_targets (L : List (BalanceEvent preset)) :
    (L.map BalanceEvent.credits).sum ≤
      ((Finset.range ((L.map fun e => e.after.state.balances.data.size).foldr max 0)).sum fun i =>
        (L.map (keyCredit i)).sum) := by
  have comm : (L.map fun e =>
      ∑ j ∈ Finset.range ((L.map fun e => e.after.state.balances.data.size).foldr max 0),
        keyCredit j e).sum =
      ∑ j ∈ Finset.range ((L.map fun e => e.after.state.balances.data.size).foldr max 0),
        (L.map (keyCredit j)).sum := by
    have := Multiset.sum_map_sum (m := (↑L : Multiset (BalanceEvent preset)))
      (s := Finset.range ((L.map fun e => e.after.state.balances.data.size).foldr max 0))
      (f := fun e j => keyCredit j e)
    exact this
  rw [← comm]
  refine List.sum_le_sum fun e member => ?_
  exact Finset.sum_le_sum_of_subset (Finset.range_mono
    (Base.le_foldr_max (List.mem_map_of_mem (f := fun e : BalanceEvent preset =>
      e.after.state.balances.data.size) member)))

/-- The credits of the balances from one state to another, over the later balances. -/
private def credited {f : Fork} (s t : BeaconState preset f) : ℕ :=
  ∑ j ∈ Finset.range t.balances.data.size,
    (actualBalanceAt ⟨f, t⟩ j - actualBalanceAt ⟨f, s⟩ j)

/-- The credits of the balances at some positions, from one state to another. -/
private def creditedAt {f : Fork} (T : Finset ℕ) (s t : BeaconState preset f) : ℕ :=
  ∑ j ∈ T, (actualBalanceAt ⟨f, t⟩ j - actualBalanceAt ⟨f, s⟩ j)

/-- The credits at some positions telescope along two steps. -/
private theorem creditedAt_trans {f : Fork} (T : Finset ℕ) {a b c : BeaconState preset f} :
    creditedAt T a c ≤ creditedAt T a b + creditedAt T b c := by
  unfold creditedAt
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => by omega

private theorem credited_trans {f : Fork} {a b c : BeaconState preset f}
    (ab : b.balances.data.size = a.balances.data.size)
    (bc : c.balances.data.size = b.balances.data.size) :
    credited a c ≤ credited a b + credited b c := by
  have _ := ab
  show creditedAt (Finset.range c.balances.data.size) a c ≤
    creditedAt (Finset.range b.balances.data.size) a b +
      creditedAt (Finset.range c.balances.data.size) b c
  rw [bc]
  exact creditedAt_trans _

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

/-- One transfer of a pass credits at most the amount moved. -/
private theorem credited_transfer {f : Fork} {s lowered raised : BeaconState preset f}
    {source target : ValidatorIndex} {moved : Gwei}
    (lowerOk : decreaseBalance s source moved = .ok lowered)
    (raiseOk : increaseBalance lowered target moved = .ok raised) :
    credited s raised ≤ moved.toNat := by
  have bound := creditedAt_transfer (Finset.range raised.balances.data.size) lowerOk raiseOk
  refine Nat.le_trans bound ?_
  split <;> omega

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

/-! ## The queue of pending consolidations over a block -/

/-- A pass credits at most the effective balances of the unslashed due sources it reads.

It keeps the registry and the number of balances. -/
private theorem pass_credits_le {f : Fork} (next : Epoch) :
    ∀ (items : List PendingConsolidation) {s t : BeaconState preset f} {read : ℕ},
      passPendingConsolidations next s items = .ok (t, read) →
      t.validators = s.validators ∧ t.balances.data.size = s.balances.data.size ∧
        credited s t ≤ ((items.take read).map (sourceBound s next)).sum := by
  intro items s t read passed
  obtain ⟨validators, sizes, credits⟩ :=
    pass_credits_le_targets next (Finset.range t.balances.data.size) items passed
  exact ⟨validators, sizes,
    credits.trans ((List.filter_sublist.map _).sum_le_sum fun _ _ => Nat.zero_le _)⟩

/-- The queue only grows at its end inside a block.

Each new entry has a source whose exit is assigned after the current epoch. -/
private def Grows {f : Fork} (s t : BeaconState preset f) : Prop :=
  ∀ electra : .pectra ≤ f, ∃ added : List PendingConsolidation,
    (t.pendingConsolidations electra).data.toList =
      (s.pendingConsolidations electra).data.toList ++ added ∧
    ∀ c ∈ added, ∃ w, t.validators.data[c.sourceIndex.toNat]? = some w ∧
      getCurrentEpoch s < w.exitEpoch ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH

private theorem Grows.of_same {f : Fork} {s t : BeaconState preset f}
    (queue : .pectra ≤ f → SamePendingQueue s t) : Grows s t := by
  intro electra
  refine ⟨[], ?_, fun _ member => by simp at member⟩
  rw [show t.pendingConsolidations electra = s.pendingConsolidations electra from
    congrFun (queue electra) electra, List.append_nil]

private theorem Grows.trans {f : Fork} {s u t : BeaconState preset f}
    (one : Grows s u) (two : Grows u t) (life : RegistryLifecycle u t)
    (slot : u.slot = s.slot) : Grows s t := by
  intro electra
  obtain ⟨added, queue, new⟩ := one electra
  obtain ⟨added', queue', new'⟩ := two electra
  have epoch : getCurrentEpoch u = getCurrentEpoch s := by simp only [getCurrentEpoch, slot]
  refine ⟨added ++ added', by rw [queue', queue, List.append_assoc], fun c member => ?_⟩
  rcases List.mem_append.mp member with old | fresh
  · obtain ⟨w, read, later, assigned⟩ := new c old
    obtain ⟨w', read', kept⟩ := life.validators _ w read
    have exit := kept.exitEpoch assigned
    exact ⟨w', read', by rw [exit]; exact later, by rw [exit]; exact assigned⟩
  · obtain ⟨w, read, later, assigned⟩ := new' c fresh
    exact ⟨w, read, epoch ▸ later, assigned⟩

/-- A block step: master's frame and lifecycle, and the growth of the queue. -/
private def GrowStep {f : Fork} (s t : BeaconState preset f) : Prop :=
  Frame s t ∧ RegistryLifecycle s t ∧ Grows s t

private theorem GrowStep.of_same {f : Fork} {s t : BeaconState preset f} (frame : Frame s t)
    (life : RegistryLifecycle s t) (queue : .pectra ≤ f → SamePendingQueue s t) :
    GrowStep s t :=
  ⟨frame, life, Grows.of_same queue⟩

private theorem GrowStep.of_data {f : Fork} {s t : BeaconState preset f} (frame : Frame s t)
    (same : t.validators.data = s.validators.data)
    (queue : .pectra ≤ f → SamePendingQueue s t) : GrowStep s t :=
  GrowStep.of_same frame (RegistryLifecycle.of_data same) queue

private theorem GrowStep.refl {f : Fork} (s : BeaconState preset f) : GrowStep s s :=
  GrowStep.of_data (Frame.refl s) rfl fun _ => rfl

private theorem GrowStep.trans {f : Fork} {s u t : BeaconState preset f}
    (one : GrowStep s u) (two : GrowStep u t) : GrowStep s t :=
  ⟨one.1.trans two.1, one.2.1.trans two.2.1, one.2.2.trans two.2.2 two.2.1 one.1.slot⟩

private theorem GrowStep.fold {f : Fork} {s t : BeaconState preset f} {α ε : Type}
    {step : BeaconState preset f → α → Except ε (BeaconState preset f)} {xs : List α}
    (kept : ∀ a item b, step a item = .ok b → GrowStep a b)
    (ok : xs.foldlM step s = .ok t) : GrowStep s t :=
  foldlM_ok_invariant (GrowStep s)
    (fun _ _ _ prior computed => prior.trans (kept _ _ _ computed)) (GrowStep.refl s) ok

section GrowSteps

variable {f : Fork} {s t : BeaconState preset f}

private theorem growStep_processProposerSlashing {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t) : GrowStep s t :=
  GrowStep.of_same (frame_processProposerSlashing ok).toFrame
    (registryLifecycle_processProposerSlashing ok) (fun _ => SamePendingQueue.proposer ok)

private theorem growStep_processAttesterSlashing {slashing : AttesterSlashing preset f}
    (ok : processAttesterSlashing config checks s slashing = .ok t) : GrowStep s t :=
  GrowStep.of_same (frame_processAttesterSlashing ok).toFrame
    (registryLifecycle_processAttesterSlashing ok) (fun _ => SamePendingQueue.attester ok)

private theorem growStep_processAttestation {attestation : Attestation preset f} {parent : Slot}
    (ok : processAttestation config checks s parent attestation = .ok t) : GrowStep s t :=
  GrowStep.of_data (frame_processAttestation ok)
    (congrArg (·.data) (processAttestation_registry ok).1)
    (fun electra => SamePendingQueue.attestation electra ok)

private theorem growStep_processDeposit {before : f < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) : GrowStep s t :=
  GrowStep.of_same (frame_processDeposit ok).toFrame (registryLifecycle_processDeposit ok)
    (fun electra => SamePendingQueue.deposit electra ok)

private theorem growStep_processVoluntaryExit {signed : SignedVoluntaryExit}
    (ok : processVoluntaryExit config checks s signed = .ok t) : GrowStep s t :=
  GrowStep.of_same (frame_processVoluntaryExit ok).toFrame
    (registryLifecycle_processVoluntaryExit ok) (fun _ => SamePendingQueue.voluntary ok)

private theorem growStep_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) : GrowStep s t :=
  GrowStep.of_same (frame_processBlsToExecutionChange ok).toFrame
    (registryLifecycle_processBlsToExecutionChange ok) (fun _ => SamePendingQueue.bls ok)

private theorem growStep_processDepositRequest {electra : .pectra ≤ f} {request : DepositRequest}
    (ok : processDepositRequest s electra request = .ok t) : GrowStep s t :=
  GrowStep.of_data (frame_processDepositRequest ok).toFrame
    (congrArg (·.data) (processDepositRequest_ok ok).2.1)
    (fun _ => SamePendingQueue.depositRequest ok)

private theorem growStep_processWithdrawalRequest {electra : .pectra ≤ f}
    {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) : GrowStep s t :=
  GrowStep.of_same (frame_processWithdrawalRequest ok).toFrame
    (registryLifecycle_processWithdrawalRequest ok)
    (fun _ => SamePendingQueue.withdrawalRequest ok)

/-- A queued consolidation assigns its source an exit after the current epoch. -/
private theorem grows_queueConsolidation {electra : .pectra ≤ f}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    Grows s t := by
  obtain ⟨churned, written, epoch, withdrawal, -, assigned, later, -, set, validators, pushed⟩ :=
    queueConsolidation_queued delay ok
  intro electra'
  refine ⟨[⟨sourceIndex, targetIndex⟩], ?_, fun c member => ?_⟩
  · exact pushed
  · rw [List.mem_singleton] at member
    subst member
    rw [validators]
    exact ⟨_, getValidator_eq_ok_iff.mp (getValidator_setValidator_self set), later, assigned⟩

/-- A consolidation request switches credentials or queues a consolidation. -/
private theorem growStep_processConsolidationRequest {electra : .pectra ≤ f}
    {request : ConsolidationRequest}
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : processConsolidationRequest config s electra request = .ok t) : GrowStep s t := by
  have frame := (frame_processConsolidationRequest ok).toFrame
  have life := registryLifecycle_processConsolidationRequest ok
  suffices new : Grows s t from ⟨frame, life, new⟩
  clear frame life
  unfold processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals try first
    | (cases ok; done)
    | (cases ok; exact Grows.of_same fun _ => rfl)
    | exact Grows.of_same fun _ => SamePendingQueue.compounding (liftAccessor_ok.mp ok)
  exact grows_queueConsolidation delay ok

private theorem growStep_processExecutionRequests {body : BeaconBlockBody preset f}
    {electra : .pectra ≤ f ∧ f < .glamsterdam}
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : processExecutionRequests config s body electra = .ok t) : GrowStep s t := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := ok
  exact (GrowStep.fold (fun _ _ _ ok => growStep_processDepositRequest ok) deposits).trans <|
    (GrowStep.fold (fun _ _ _ ok => growStep_processWithdrawalRequest ok) withdrawals).trans
      (GrowStep.fold (fun _ _ _ ok => growStep_processConsolidationRequest delay ok)
        consolidations)

private theorem growStep_processOperations {body : BeaconBlockBody preset f} {parent : Slot}
    (early : f < .glamsterdam) (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : processOperations config checks s body parent = .ok t) :
    GrowStep s t := by
  unfold processOperations at ok
  rw [dite_eq_right (show ¬ .glamsterdam ≤ f from Nat.not_le_of_lt early)] at ok
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, _, _, _, _, proposers, _, attesters, _, attested, _, deposits, exited,
    exits, changed, changes, requests⟩ := ok
  have c : GrowStep exited changed := by
    unfold processBlsToExecutionChanges at changes
    split at changes
    · rw [← Array.foldlM_toList] at changes
      exact GrowStep.fold (fun _ _ _ ok => growStep_processBlsToExecutionChange ok) changes
    · cases changes; exact GrowStep.refl _
  have r : GrowStep changed t := by
    split at requests
    · exact growStep_processExecutionRequests delay requests
    · cases requests; exact GrowStep.refl _
  exact (GrowStep.fold (fun _ _ _ ok => growStep_processProposerSlashing ok) proposers).trans <|
    (GrowStep.fold (fun _ _ _ ok => growStep_processAttesterSlashing ok) attesters).trans <|
    (GrowStep.fold (fun _ _ _ ok => growStep_processAttestation ok) attested).trans <|
    (GrowStep.fold (fun _ _ _ ok => growStep_processDeposit ok) deposits).trans <|
    (GrowStep.fold (fun _ _ _ ok => growStep_processVoluntaryExit ok) exits).trans <|
    c.trans r

/-- A block from Altair and before Gloas keeps the frame and the lifecycle.

It also grows the queue. -/
private theorem growStep_processBlock {engine : ExecutionEngine preset f}
    {block : BeaconBlock preset f} (altair : .altair ≤ f) (early : f < .glamsterdam)
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : processBlock config checks engine s block = .ok t) : GrowStep s t := by
  unfold processBlock at ok
  simp only [altair, ↓reduceDIte] at ok
  unfold processBlockAltair at ok
  simp only [stateBeforeOperations, bind_assoc, bind_ok_iff] at ok
  obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
    votedOk, operated, operatedOk, synced⟩ := ok
  rw [dite_eq_right (show ¬ .glamsterdam ≤ f from Nat.not_le_of_lt early)] at paidOk
  cases paidOk
  have header : GrowStep s headed := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
    exact GrowStep.of_data (frame_processBlockHeader headedOk).toFrame rfl fun _ => rfl
  have e : GrowStep headed executed := by
    split at executedOk
    · exact GrowStep.of_data (frame_processBlockExecution executedOk).toFrame
        (congrArg (·.data) (processBlockExecution_validators executedOk))
        (fun _ => SamePendingQueue.blockExecution early executedOk)
    · cases executedOk; exact GrowStep.refl _
  have randao : GrowStep executed revealed := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealedOk
    exact GrowStep.of_data (frame_processRandao revealedOk).toFrame rfl fun _ => rfl
  have v : GrowStep revealed voted := by
    split at votedOk
    · obtain ⟨_, _, rest⟩ := processEth1Data_eq votedOk
      exact GrowStep.of_data (frame_processEth1Data votedOk).toFrame (by rw [← rest])
        (fun _ => by unfold SamePendingQueue; rw [← rest])
    · cases votedOk; exact GrowStep.refl _
  have sync : GrowStep operated t := by
    have frame := (frame_processSyncAggregate synced).toFrame
    obtain ⟨balances, rfl⟩ := processSyncAggregate_eq synced
    exact GrowStep.of_data frame rfl fun _ => rfl
  exact header.trans <| e.trans <| randao.trans <| v.trans <|
    (growStep_processOperations early delay operatedOk).trans sync

end GrowSteps

/-! ## The queue of a run from X, and the stake a pass can move -/

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

/-- A state of any fork with the same queue and a later life of its validators has the shape. -/
private theorem Shape.carry {L : List PendingConsolidation} {e0 : Epoch} {n : ℕ} {f g : Fork}
    {a : BeaconState preset f} {b : BeaconState preset g} (shape : Shape L e0 n a)
    (queue : fundingSources b = fundingSources a) (life : RegistryLifecycle a b) :
    Shape L e0 n b := by
  obtain ⟨N, eq, new⟩ := shape
  refine ⟨N, queue.trans eq, fun c member => ?_⟩
  obtain ⟨w, read, later, assigned⟩ := new c member
  obtain ⟨w', read', kept⟩ := life.validators _ w read
  have exit := kept.exitEpoch assigned
  exact ⟨w', read', by rw [exit]; exact later, by rw [exit]; exact assigned⟩

/-- A block that grows the queue keeps the shape. -/
private theorem Shape.grow {L : List PendingConsolidation} {e0 : Epoch} {n : ℕ} {f : Fork}
    {a b : BeaconState preset f} (electra : .pectra ≤ f) (shape : Shape L e0 n a)
    (grows : Grows a b) (life : RegistryLifecycle a b) (started : e0 ≤ getCurrentEpoch a) :
    Shape L e0 n b := by
  obtain ⟨N, eq, new⟩ := shape
  obtain ⟨added, queue, fresh⟩ := grows electra
  refine ⟨N ++ added, by rw [fundingSources_eq electra, queue, ← fundingSources_eq electra, eq,
    List.append_assoc], fun c member => ?_⟩
  rcases List.mem_append.mp member with old | recent
  · obtain ⟨w, read, later, assigned⟩ := new c old
    obtain ⟨w', read', kept⟩ := life.validators _ w read
    have exit := kept.exitEpoch assigned
    exact ⟨w', read', by rw [exit]; exact later, by rw [exit]; exact assigned⟩
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
  · obtain ⟨w, read, later, assigned⟩ := new c (List.mem_of_mem_drop member)
    obtain ⟨w', read', kept⟩ := life.validators _ w read
    have exit := kept.exitEpoch assigned
    exact ⟨w', read', by rw [exit]; exact later, by rw [exit]; exact assigned⟩

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

/-- A pass, from a state with the shape, credits at most the caps at X of the entries it reads. -/
private theorem pass_step {x : ForkedBeaconState preset} {high : ℕ} {f : Fork}
    {p t : BeaconState preset f} {n : ℕ} (facts : PassFacts (config := config) x high p)
    (shape : Shape (x.state.pendingConsolidations facts.electraX).data.toList
      (getCurrentEpoch x.state) n p)
    (computed : processPendingConsolidations p facts.electraP = .ok t) :
    ∃ r, Shape (x.state.pendingConsolidations facts.electraX).data.toList
        (getCurrentEpoch x.state) (n + r) t ∧ RegistryLifecycle p t ∧
      credited p t ≤
        ((((x.state.pendingConsolidations facts.electraX).data.toList.drop n).take r).map
          (capBound x high)).sum := by
  obtain ⟨r, shapeT, life, credits⟩ := pass_step_targets facts shape computed
  exact ⟨r, shapeT, life, (credits (Finset.range t.balances.data.size)).trans
    ((List.filter_sublist.map _).sum_le_sum fun _ _ => Nat.zero_le _)⟩

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
      ∀ e ∈ post.2, e.source ≠ .consolidations := by
    simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨⟨credit, debit⟩, _, t, _, rfl⟩ := ok
    intro e member
    rcases List.mem_append.mp member with old | new
    · exact initial e old
    · exact (List.mem_singleton.mp new) ▸ notConsolidation
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
          (T.sum fun i => ((events.filter (·.source = .consolidations)).map (keyCredit i)).sum) ≤
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
    have divides : preset.SLOTS_PER_EPOCH.toNat ∣ m.state.slot.toNat + 1 := by
      rw [← sum]
      exact Nat.dvd_of_mod_eq_zero (by simpa using congrArg UInt64.toNat boundary)
    have epochLast : (getCurrentEpoch last.state).toNat = (getCurrentEpoch m.state).toNat + 1 := by
      have advancedEpoch : getCurrentEpoch last.state = getCurrentEpoch
          ({ epoched with slot := next } : BeaconState preset m.fork) := by
        rw [afterEq]
        exact congrArg (computeEpochAtSlot preset) (processUpgrades_slot upgrades)
      rw [advancedEpoch]
      have nextEpoch :=
        getCurrentEpoch_toNat ({ epoched with slot := next } : BeaconState preset m.fork)
      simp only at nextEpoch
      rw [nextEpoch, sum, Nat.succ_div_of_dvd divides, getCurrentEpoch_toNat m.state]
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
      simpa [List.filter_cons, creditedAt, keyCredit, actualBalanceAt] using credits T
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

/-- A slot step moves the shape of the queue on, and its consolidation credits are bounded. -/
private theorem slot_step {g x m last : ForkedBeaconState preset}
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
        ((events.filter (·.source = .consolidations)).map BalanceEvent.credits).sum ≤
          ((((queueX x electra).drop n).take r).map (capBound x high)).sum := by
  obtain ⟨r, shapeLast, credits⟩ := slot_step_targets shared pre genesis caps delay electra high
    within ok early endEpoch shape
  refine ⟨r, shapeLast, fun {events} replayed => ?_⟩
  exact (credits_sum_le_targets _).trans ((credits replayed _).trans
    ((List.filter_sublist.map _).sum_le_sum fun _ _ => Nat.zero_le _))

/-- A block keeps the shape of the queue: it only appends entries that are new since X. -/
private theorem block_step {f : Fork} {e0 : Epoch} {L : List PendingConsolidation} {n : ℕ}
    (electra : .pectra ≤ f) (early : f < .glamsterdam)
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {engine : ExecutionEngine preset f} {signed : SignedBeaconBlock preset f}
    {s t : BeaconState preset f}
    (ok : applySignedBlock config checks engine s signed true = .ok t)
    (started : e0 ≤ getCurrentEpoch s) (shape : Shape L e0 n s) : Shape L e0 n t := by
  have grown := growStep_processBlock (Nat.le_trans (by decide) electra) early delay
    (applySignedBlock_ok ok).2.1
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
        (T.sum fun i => ((events.filter (·.source = .consolidations)).map (keyCredit i)).sum) ≤
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
          (T.sum fun i => ((added.filter (·.source = .consolidations)).map (keyCredit i)).sum) ≤
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

/-- The consolidation credits of a run from X are within the caps of the entries it reads. -/
private theorem run_credits {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (electra : .pectra ≤ x.fork) (high : ℕ)
    (within : high + 2 ≤ (getCurrentEpoch x.state).toNat +
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    ∃ n, Shape (queueX x electra) (getCurrentEpoch x.state) n y.state ∧
      ((events.filter (·.source = .consolidations)).map BalanceEvent.credits).sum ≤
        (((queueX x electra).take n).map (capBound x high)).sum := by
  obtain ⟨n, shape, bound⟩ := run_credits_targets shared genesis caps delay electra high within
    tail early endEpoch replayed
  exact ⟨n, shape, (credits_sum_le_targets _).trans
    ((bound _).trans ((List.filter_sublist.map _).sum_le_sum fun _ _ => Nat.zero_le _))⟩

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

/-! ## Group A: credits to exiting keys -/

/-- A1 (item 14, run lift).

Along C's run, no deposit credits a key that exits at the run's start.

The key stays not withdrawable through the run's end.

`kept` is the withdrawable-kept fact at the state before each deposit event of a slot step.

A block deposit needs none: from Electra it raises no balance.

It says that an assigned exit stays (`RegistryLifecycle`).

It says that once the exit is set, the withdrawable epoch only rises (`WithdrawableKept`).

The private sources of these facts are `WithdrawalKept` in PendingConsolidations.

The other private source is `Lives` in BranchLedger.

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
    ((events.filter (·.source = .deposits)).map (keyCredit i)).sum = 0 := by
  have located := run_located tail electra early high replayed
  apply List.sum_eq_zero
  intro n member
  obtain ⟨e, filtered, rfl⟩ := List.mem_map.mp member
  obtain ⟨inEvents, sourceEq⟩ := List.mem_filter.mp filtered
  simp only [decide_eq_true_eq] at sourceEq
  rcases located e inEvents sourceEq with unconditional | ⟨u, w, ok, es, contains, replayedEs,
      inStep, keeps⟩
  · have := unconditional i
    simp only [keyCredit]
    omega
  · obtain ⟨life, withdrawal, epoch⟩ := kept ok contains replayedEs e inStep sourceEq
    obtain ⟨w, read, lifecycle⟩ := life.validators i v found
    have assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
      rw [far] at exited
      exact absurd exited (Nat.lt_irrefl _)
    have sameExit := lifecycle.exitEpoch assigned
    have later := UInt64.le_iff_toNat_le.mp (withdrawal i v w found read assigned).1
    have now := UInt64.le_iff_toNat_le.mp epoch
    have same := keeps i w read (by rw [sameExit]; exact exited) (by omega)
    simp [keyCredit, actualBalanceAt, same]

/-- Along C's run from Fulu, no deposit credits a key that exits at the run's start.

The key stays not withdrawable through the run's end.

The withdrawable-kept fact at each deposit event of a slot step is `Run.events_kept`. -/
private theorem Run.exiting_deposit_credit_zero {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (fulu : .fusaka ≤ x.fork) (early : y.fork < .glamsterdam)
    (high : ℕ) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (i : ℕ) (v : Validator) (found : x.state.validators.data[i]? = some v)
    (exited : v.exitEpoch.toNat < 2 ^ 64 - 1)
    (held : (getCurrentEpoch y.state).toNat < v.withdrawableEpoch.toNat) :
    ((events.filter (·.source = .deposits)).map (keyCredit i)).sum = 0 :=
  Run.exiting_deposit_credit_zero_of_kept tail (Nat.le_trans (by decide) fulu) early high replayed
    (fun {_ _} ok contained {_} replayedEs =>
      PinSplit4.Run.events_kept shared genesis tail fulu early ok contained replayedEs)
    i v found exited held

/-- A2'' (rev 2.5.1).

Take a run from X whose last epoch is within the withdrawal delay of X's.

The consolidation credits to all keys along it are at most a sum of caps.

The sum is over the sources of X's pending consolidations.

They are unslashed at X and withdrawable by `high + 1`.

Each source counts at its cap at X.

An entry requested after X is due only past the run, so every applied entry is in X's queue.

It moves at most the source's effective balance, which is at most its cap.

An exited key cannot switch to compounding, so its cap does not rise after X. -/
private theorem Run.consolidation_credits_le_X {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset)
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (high : ℕ) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (withinDelay : high + 2 ≤
      (getCurrentEpoch x.state).toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    ((events.filter (·.source = .consolidations)).map BalanceEvent.credits).sum ≤
      ((((x.state.pendingConsolidations electra).data.toList.filterMap fun c =>
        x.state.validators.data[c.sourceIndex.toNat]?).filter fun v =>
          !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)).map fun v =>
            (withdrawalMaxEffectiveBalance preset x.fork v).toNat).sum := by
  obtain ⟨n, -, bound⟩ := run_credits shared genesis caps delay electra high withinDelay tail
    early endEpoch replayed
  rw [← capBound_sum]
  refine Nat.le_trans bound ?_
  have split := List.take_append_drop n (x.state.pendingConsolidations electra).data.toList
  conv_rhs => rw [← split, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

/-- A2'' for a set of targets.

The consolidation credits to the keys in `T` along the run of `Run.consolidation_credits_le_X`.

They are at most the caps at X of the due entries of X's queue whose target is in `T`.

Each entry credits only its target, so the sum over the entries splits by target. -/
private theorem Run.consolidation_credits_le_X_targets {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset)
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (high : ℕ) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (withinDelay : high + 2 ≤
      (getCurrentEpoch x.state).toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) (T : Finset ℕ) :
    (T.sum fun i => ((events.filter (·.source = .consolidations)).map (keyCredit i)).sum) ≤
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
end PinSplit

end GroupA

section GroupC

/-! ## PinExitQueue -/

namespace PinSplit

open Base Uint64 Models DirectSafety

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-! ## Group C: exit counts, gain rate, new keys, preset facts (items 15, 16, new-key step, N6) -/

/-! ## A validator created in a step has no exit assigned -/

/-- Every validator from position `n` on has no exit epoch assigned. -/
private def ExitFarFrom (n : ℕ) {f : Fork} (s : BeaconState preset f) : Prop :=
  ∀ i v, n ≤ i → s.validators.data[i]? = some v → v.exitEpoch = FAR_FUTURE_EPOCH

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
        ⟨kept.1.of_data (PinSplit4.upgradeNext_validators kept.2 ok),
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
private theorem Run.charge_of_exit {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (i : ℕ) (unset : ∀ v, x.state.validators.data[i]? = some v → v.exitEpoch = FAR_FUTURE_EPOCH)
    (v : Validator) (found : y.state.validators.data[i]? = some v)
    (assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    ∃ c ∈ tail.departureCharges, c.index = i ∧ c.epoch = v.exitEpoch.toNat := by
  induction tail generalizing v with
  | nil => exact absurd (unset v found) assigned
  | @snoc middle last pre step ih =>
    have middleEarly : middle.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have middleElectra : .pectra ≤ middle.fork :=
      Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
    cases present : middle.state.validators.data[i]? with
    | none =>
      have outside : middle.state.validators.data.size ≤ i :=
        Array.getElem?_eq_none_iff.mp present
      exact absurd (ExitFarFrom.of_chainStep step.chainStep middleElectra middleEarly i v outside
        found) assigned
    | some w =>
      by_cases pending : w.exitEpoch = FAR_FUTURE_EPOCH
      · obtain ⟨charge, member, index, epoch⟩ :=
          (Run.nil.snoc step).departure_charge_of_assigned i w v present found pending assigned
        exact ⟨charge, List.mem_append_right _ member, index, epoch⟩
      · obtain ⟨charge, member, index, epoch⟩ :=
          ih middleEarly w present pending
        obtain ⟨u, usedFound, kept⟩ :=
          (RegistryLifecycle.chainStep step.chainStep).validators i w present
        have same : u = v := Option.some.inj (usedFound.symm.trans found)
        refine ⟨charge, List.mem_append_left _ member, index, ?_⟩
        rw [epoch, ← same, kept.exitEpoch pending]

/-- Every departure charge of a run reads the effective balance of a state on its balance path.

It reads it at the charged position. -/
private theorem Run.charge_amount_mem {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (c : DepartureCharge) (member : c ∈ tail.departureCharges) :
    ∃ z ∈ tail.balancePath, effectiveAt z c.index = c.amount := by
  induction tail with
  | nil => simp [Run.departureCharges] at member
  | @snoc middle last pre step ih =>
    rcases List.mem_append.mp member with earlier | latest
    · obtain ⟨z, inPath, same⟩ := ih earlier
      exact ⟨z, by simp [Run.balancePath, inPath], same⟩
    · obtain ⟨⟨old, i⟩, present, added⟩ := List.mem_filterMap.mp latest
      dsimp only at added
      split at added
      · cases added
      · split at added
        · cases Option.some.inj added
          refine ⟨middle, ?_, ?_⟩
          · exact List.mem_append_right _ (List.mem_of_mem_head? step.balancePath_ends.1)
          · have found := (List.mem_zipIdx_iff_getElem?.mp present)
            rw [Array.getElem?_toList] at found
            simp [effectiveAt, found]
        · cases added

/-- The input of a step of a run lies on the run's balance path.

Its fork is no earlier than the run's first. -/
private theorem Run.input_mem_path {x y u w : ForkedBeaconState preset}
    {tail : Run config checks x y} {step : Step config checks u w} (member : tail.Contains step) :
    u ∈ tail.balancePath ∧ x.fork ≤ u.fork := by
  induction member with
  | last pre step =>
    refine ⟨?_, fork_le_of_chainSteps pre.chainSteps⟩
    exact List.mem_append_right _ (List.mem_of_mem_head? step.balancePath_ends.1)
  | earlier member next ih =>
    exact ⟨List.mem_append_left _ ih.1, ih.2⟩

/-- C1' (item 15, corrected).

Count the keys whose exit starts along C's run, with an exit epoch at most `high + 1`.

Each has an effective balance of at least `bound` along the run.

Each spends at least `bound` of the exit and consolidation queues' room up to epoch `high + 1`.

So their number times `bound` is at most the carry of both queues plus their churn per epoch.

The window bound is `departure_charges_le_window_electra_cap` (DepartureQueue). -/
private theorem Run.exits_started_le {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam) (high bound churn : ℕ)
    (consolidationChurn : ℕ) (positive : 0 < bound)
    (churnOk : ∀ z ∈ tail.balancePath, ∀ c : Gwei,
      (if .pectra ≤ z.fork then exitChurnLimit config z.state else .ok 0) = .ok c →
        c.toNat ≤ churn)
    (consolidationChurnOk : ∀ site ∈ tail.consolidationSites,
      ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
        getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ consolidationChurn) :
    ((Finset.range y.state.validators.data.size).filter fun i =>
      ((x.state.validators.data[i]?).map (·.exitEpoch)).getD FAR_FUTURE_EPOCH = FAR_FUTURE_EPOCH ∧
      ((y.state.validators.data[i]?).map (·.exitEpoch)).getD FAR_FUTURE_EPOCH ≠ FAR_FUTURE_EPOCH ∧
      ((y.state.validators.data[i]?).map (·.exitEpoch.toNat)).getD 0 ≤ high + 1 ∧
      ∀ z ∈ tail.balancePath, bound ≤ effectiveAt z i).card * bound ≤
      (if (x.state.earliestExitEpoch electra).toNat ≤ high + 1 then
        (x.state.exitBalanceToConsume electra).toNat else 0) +
      (if (x.state.earliestConsolidationEpoch electra).toNat ≤ high + 1 then
        (x.state.consolidationBalanceToConsume electra).toNat else 0) +
      (high + 2 - max (getCurrentEpoch x.state).toNat (x.state.earliestExitEpoch electra).toNat) *
        churn +
      (high + 2 - max (getCurrentEpoch x.state).toNat
        (x.state.earliestConsolidationEpoch electra).toNat) * consolidationChurn := by
  classical
  have _ := positive
  refine Nat.le_trans ?_ (departure_charges_le_window_electra_cap tail electra early high
    consolidationChurn churn ?_ consolidationChurnOk)
  swap
  · -- The input of each step lies on the balance path, at a fork from Electra.
    intro u w step member rate computed
    obtain ⟨onPath, forks⟩ := Run.input_mem_path member
    have fromElectra : .pectra ≤ u.fork := Nat.le_trans electra forks
    exact churnOk u onPath rate (by simpa only [fromElectra, ↓reduceIte] using computed)
  set kept := tail.departureCharges.filter fun c => c.epoch ≤ high + 1 with kept_def
  set chosen := (Finset.range y.state.validators.data.size).filter fun i =>
      ((x.state.validators.data[i]?).map (·.exitEpoch)).getD FAR_FUTURE_EPOCH = FAR_FUTURE_EPOCH ∧
      ((y.state.validators.data[i]?).map (·.exitEpoch)).getD FAR_FUTURE_EPOCH ≠ FAR_FUTURE_EPOCH ∧
      ((y.state.validators.data[i]?).map (·.exitEpoch.toNat)).getD 0 ≤ high + 1 ∧
      ∀ z ∈ tail.balancePath, bound ≤ effectiveAt z i with chosen_def
  -- Each chosen key has a charge in the window at its position.
  have charged : ∀ i ∈ chosen, ∃ c ∈ kept, c.index = i := by
    intro i member
    simp only [chosen_def, Finset.mem_filter, Finset.mem_range] at member
    obtain ⟨inside, unset, assigned, within, _⟩ := member
    obtain ⟨current, found⟩ := Option.isSome_iff_exists.mp
      (by simpa using inside : (y.state.validators.data[i]?).isSome)
    simp only [found, Option.map_some, Option.getD_some] at assigned within
    obtain ⟨c, listed, index, epoch⟩ := Run.charge_of_exit tail electra early i
      (fun w located => by simpa [located] using unset) current found assigned
    exact ⟨c, List.mem_filter.mpr ⟨listed, by simpa [epoch] using within⟩, index⟩
  -- Those charges each spend at least `bound`.
  let owned := kept.filter fun c => decide (c.index ∈ chosen)
  have cardLe : chosen.card ≤ owned.length := by
    have covered : chosen ⊆ (owned.map (·.index)).toFinset := by
      intro i member
      obtain ⟨c, listed, index⟩ := charged i member
      simp only [List.mem_toFinset, List.mem_map, owned, List.mem_filter, decide_eq_true_eq]
      exact ⟨c, ⟨listed, index ▸ member⟩, index⟩
    exact (Finset.card_le_card covered).trans ((List.toFinset_card_le _).trans (by simp))
  have enough : ∀ a ∈ owned.map (·.amount), bound ≤ a := by
    intro a member
    obtain ⟨c, listed, rfl⟩ := List.mem_map.mp member
    simp only [owned, List.mem_filter, decide_eq_true_eq, kept_def] at listed
    obtain ⟨⟨inPath, -⟩, chosenKey⟩ := listed
    obtain ⟨z, onPath, amount⟩ := Run.charge_amount_mem tail c inPath
    simp only [chosen_def, Finset.mem_filter] at chosenKey
    rw [← amount]
    exact chosenKey.2.2.2.2 z onPath
  have owns : owned.length * bound ≤ (owned.map (·.amount)).sum := by
    simpa using List.length_nsmul_le_sum _ _ enough
  have sub : (owned.map (·.amount)).sum ≤ (kept.map (·.amount)).sum :=
    ((List.filter_sublist).map _).sum_le_sum fun _ _ => Nat.zero_le _
  exact (Nat.mul_le_mul_right bound cardLe).trans (owns.trans sub)

/-- C2 (item 16).

Every key's gain rate is at most the gain rate at the largest effective balance.

The effective balance of a key is at most `MAX_EFFECTIVE_BALANCE_ELECTRA`. -/
private theorem gain_le_capMax (perIncrement eb : ℕ)
    (capped : eb ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat) :
    eb / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * perIncrement *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat ≤
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum /
          WEIGHT_DENOMINATOR.toNat :=
  Nat.div_le_div_right
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.div_le_div_right capped)))

/-- C4 (preset facts, mainnet).

The slashing quotients are large enough, and the ejection balance exceeds an increment.

The ejection balance less an increment fits below two thirds of the activation balance.

That bound is less the slashing penalty, the downward band and an increment. -/
private theorem preset_facts_mainnet :
    4 ≤ (parameters Preset.mainnet .fusaka).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ∧
    2 ≤ (parameters Preset.mainnet .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
    Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT.toNat < Config.mainnet.EJECTION_BALANCE.toNat ∧
    Config.mainnet.EJECTION_BALANCE.toNat - Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      2 * Preset.mainnet.MIN_ACTIVATION_BALANCE.toNat / 3 -
        Preset.mainnet.MIN_ACTIVATION_BALANCE.toNat /
          (parameters Preset.mainnet .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        Preset.mainnet.downwardBand - Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  decide

/-- C4 (preset facts, minimal preset).

The same four facts as for the mainnet preset. -/
private theorem preset_facts_minimal :
    4 ≤ (parameters Preset.minimal .fusaka).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ∧
    2 ≤ (parameters Preset.minimal .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
    Preset.minimal.EFFECTIVE_BALANCE_INCREMENT.toNat < Config.minimal.EJECTION_BALANCE.toNat ∧
    Config.minimal.EJECTION_BALANCE.toNat - Preset.minimal.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      2 * Preset.minimal.MIN_ACTIVATION_BALANCE.toNat / 3 -
        Preset.minimal.MIN_ACTIVATION_BALANCE.toNat /
          (parameters Preset.minimal .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        Preset.minimal.downwardBand - Preset.minimal.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  decide
end PinSplit

end GroupC

section GroupSeat

/-! ## PinSeatDebits -/

namespace PinSplit5

open Base Uint64 Models DirectSafety

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The participant reward of the sync committee, at the most that a total allows.

The total is within three halves of the given total.

The reward is the base rewards of the total, times the sync weight, per slot and per member.

The base rewards of a total are at most the base reward factor times its root plus 2. -/
private def syncEnvelope (preset : Preset) (total : ℕ) : ℕ :=
  preset.BASE_REWARD_FACTOR.toNat * (Nat.sqrt (3 * total / 2) + 2) *
    SYNC_REWARD_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat / preset.SLOTS_PER_EPOCH.toNat /
      preset.SYNC_COMMITTEE_SIZE.toNat

/-- The participant reward at a state is at most the envelope of a total.

The total of the state is within three halves of that total. -/
private theorem syncReward_le_envelope {fork : Fork} {s : BeaconState preset fork}
    {reward T : Gwei} (rewardOk : syncParticipantReward s = .ok reward)
    (totalOk : getTotalActiveBalance s = .ok T) (total : ℕ) (band : 2 * T.toNat ≤ 3 * total) :
    reward.toNat ≤ syncEnvelope preset total := by
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
  unfold syncEnvelope
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
private def syncSeatEnvelope (preset : Preset) (total : ℕ) : ℕ :=
  syncEnvelope preset total + syncEnvelope preset total * PROPOSER_WEIGHT.toNat /
    (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat)

/-- The credits of an event over a set of keys are at most its credits over the registry. -/
private theorem keys_credits_le (S : Finset ℕ) (e : BalanceEvent preset) :
    ∑ j ∈ S, (actualBalanceAt e.after j - actualBalanceAt e.before j) ≤ e.credits := by
  unfold BalanceEvent.credits
  refine Finset.sum_le_sum_of_ne_zero fun j _ positive => Finset.mem_range.mpr ?_
  by_contra outside
  apply positive
  simp [actualBalanceAt, Array.getElem?_eq_none (Nat.le_of_not_lt outside)]

/-- The events of a replay record no sync pass. -/
private def NoSync {fork : Fork} (pre : BalanceReplay preset fork) : Prop :=
  ∀ e ∈ pre.2, e.source ≠ .sync

private theorem NoSync.carry {fork : Fork}
    {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
    {p q : BalanceReplay preset fork} (held : NoSync p) (ok : carryBalance action p = .ok q) :
    NoSync q := by
  intro e member
  rw [(PinSplit4.carryBalance_cases ok).2] at member
  exact held e member

private theorem NoSync.record {fork : Fork} {source : BalanceSource}
    {limits : BeaconState preset fork → Except TransitionError (Nat × Nat)}
    {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
    {p q : BalanceReplay preset fork} (held : NoSync p)
    (ok : recordBalance source limits action p = .ok q) (notSync : source ≠ .sync) :
    NoSync q := by
  intro e member
  rcases (PinSplit4.recordBalance_cases ok).2 e member with old | new
  · exact held e old
  · rw [new]
    exact notSync

/-- The effective balance of a key at a state of a run from genesis is at most the largest cap. -/
private theorem effectiveAt_le_capMax {g m : ForkedBeaconState preset}
    (run : Run config checks g m) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (early : m.fork < .glamsterdam) (v : ℕ) :
    effectiveAt m v ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := by
  unfold effectiveAt
  cases found : m.state.validators.data[v]? with
  | none => simp
  | some w =>
    obtain ⟨inside, rfl⟩ := Array.getElem?_eq_some_iff.mp found
    have bound := run.effectiveBalance_capped genesis caps.activation caps.compounding early _
      (Array.getElem_mem inside)
    have activation := UInt64.le_iff_toNat_le.mp caps.activation
    have compounding := UInt64.le_iff_toNat_le.mp caps.compounding
    rw [UInt64.le_iff_toNat_le] at bound
    unfold withdrawalMaxEffectiveBalance getMaxEffectiveBalance at bound
    simp only [Option.map_some, Option.getD_some]
    split at bound
    · split at bound <;> omega
    · omega

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
      (∀ i, (rest.map (syncDebit i)).sum = 0) ∧
      (∀ i, (rest.map (syncCredit i)).sum = 0) ∧
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
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq] at syncOk
  obtain ⟨⟨credit, debit⟩, limitsOk, u, synced, rfl, rfl⟩ := syncOk
  refine ⟨consolidated.1, consolidated.2, _, credit, debit, rfl, fun i => ?_, fun i => ?_, synced⟩
  · exact List.sum_eq_zero fun x member => by
      obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
      simp [syncDebit, eleven e inside]
  · exact List.sum_eq_zero fun x member => by
      obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
      simp [syncCredit, eleven e inside]

/-- The sync debits of a block over any keys fit the participant reward of the block's total.

The sync pass is the last pass of the replay, and no other pass records a sync event.

It reads the total of the state after the block, since a sync aggregate changes only balances. -/
private theorem block_syncDebits_le {fork : Fork} {a t : BeaconState preset fork}
    (early : fork < .glamsterdam) (altair : .altair ≤ fork) {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork} {events : List (BalanceEvent preset)}
    (replay : blockBalanceReplay (config := config) (checks := checks) early engine a block =
      .ok (t, events))
    (total : ℕ) (band : ∀ T : Gwei, getTotalActiveBalance t = .ok T → 2 * T.toNat ≤ 3 * total)
    (keys : Finset ℕ) :
    ∑ i ∈ keys, (events.map (syncDebit i)).sum ≤
      preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope preset total ∧
    ∑ i ∈ keys, ((events.map (syncCredit i)).sum + (events.map (syncDebit i)).sum) ≤
      preset.SYNC_COMMITTEE_SIZE.toNat * syncSeatEnvelope preset total := by
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
    exact (Nat.add_le_add (keys_credits_le keys ⟨.sync, ⟨fork, c⟩, ⟨fork, t⟩, 0, 0⟩)
      (DirectSafety.Apriori.Internal.keys_debits_le keys
        ⟨.sync, ⟨fork, c⟩, ⟨fork, t⟩, 0, 0⟩)).trans moves
  obtain ⟨balances, rfl⟩ := processSyncAggregate_eq synced
  have reads := rewardOk
  simp only [syncParticipantReward, bind_ok_iff, liftAccessor_ok] at reads
  obtain ⟨T, totalEnd, -⟩ := reads
  have envelope := syncReward_le_envelope rewardOk totalEnd total (band T totalEnd)
  have share := syncProposer_le envelope proposerOk
  refine ⟨?_, ?_⟩
  · simp only [List.map_append, List.sum_append, silent, syncDebit, ↓reduceIte, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Nat.zero_add, Nat.add_zero]
    exact bound.trans (Nat.mul_le_mul_left _ envelope)
  · simp only [List.map_append, List.sum_append, silent, silentCredit, syncDebit, syncCredit,
      ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.zero_add,
      Nat.add_zero]
    refine movesBound.trans (Nat.mul_le_mul_left _ ?_)
    unfold syncSeatEnvelope
    omega

private theorem replayDeltas_noSync {fork : Fork} {source : BalanceSource}
    {deltas : Array Gwei × Array Gwei} {p q : BalanceReplay preset fork}
    (notSync : source ≠ .sync) (held : NoSync p) (ok : replayDeltas source deltas p = .ok q) :
    NoSync q := by
  unfold replayDeltas at ok
  refine foldlM_ok_invariant NoSync (fun r i r' previous step => ?_) held ok
  simp only [bind_ok_iff] at step
  obtain ⟨index, _, raised, raisedOk, loweredOk⟩ := step
  exact ((previous.record raisedOk (by decide)).record loweredOk notSync)

private theorem replayRewards_noSync {fork : Fork} {p q : BalanceReplay preset fork}
    (held : NoSync p) (ok : replayRewards (config := config) p = .ok q) : NoSync q := by
  unfold replayRewards at ok
  split at ok
  · simp only [pure, Except.pure, Except.ok.injEq] at ok
    subst ok
    exact held
  · simp only [bind_ok_iff] at ok
    obtain ⟨ordinary, _, inactivity, _, ok⟩ := ok
    split at ok
    · obtain ⟨middle, middleOk, lastOk⟩ := bind_ok_iff.mp ok
      have first : NoSync middle := foldlM_ok_invariant NoSync
        (fun _ _ _ previous step => replayDeltas_noSync (by decide) previous step) held middleOk
      exact replayDeltas_noSync (by decide) first lastOk
    · obtain ⟨_, _, ok⟩ := bind_ok_iff.mp ok
      obtain ⟨one, oneOk, ok⟩ := bind_ok_iff.mp ok
      obtain ⟨two, twoOk, lastOk⟩ := bind_ok_iff.mp ok
      have first := replayDeltas_noSync (by decide) held oneOk
      have middle : NoSync two := foldlM_ok_invariant NoSync
        (fun _ _ _ previous step => replayDeltas_noSync (by decide) previous step) first twoOk
      exact replayDeltas_noSync (by decide) middle lastOk

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
  · simp only [epochReplayAction] at ok
    split at ok
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨deposited, _, rfl⟩ := ok
      intro e member
      rcases List.mem_append.mp member with old | added
      · exact held e old
      · rw [List.mem_singleton.mp added]
        exact nofun
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      subst ok
      exact held
  · simp only [epochReplayAction] at ok
    split at ok
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨consolidated, _, rfl⟩ := ok
      intro e member
      rcases List.mem_append.mp member with old | added
      · exact held e old
      · rw [List.mem_singleton.mp added]
        exact nofun
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      subst ok
      exact held

/-- From Electra, a slot step records no sync pass. -/
private theorem slot_noSync {x y : ForkedBeaconState preset} (electra : .pectra ≤ x.fork)
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
    ∑ i ∈ keys, (((first ++ second).map (syncCredit i)).sum +
      ((first ++ second).map (syncDebit i)).sum) =
    ∑ i ∈ keys, ((first.map (syncCredit i)).sum + (first.map (syncDebit i)).sum) +
      ∑ i ∈ keys, ((second.map (syncCredit i)).sum + (second.map (syncDebit i)).sum) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [List.map_append, List.sum_append]
  omega

/-- A slot step neither debits nor credits a key for the sync committee. -/
private theorem slot_syncDebit_zero {x y : ForkedBeaconState preset} (electra : .pectra ≤ x.fork)
    (ok : advanceSlotAcross config checks x = .ok y) (early : y.fork < .glamsterdam)
    {events : List (BalanceEvent preset)}
    (replayed : (Step.slot ok : Step config checks x y).balanceEvents = .ok events) (i : ℕ) :
    (events.map (syncDebit i)).sum = 0 ∧ (events.map (syncCredit i)).sum = 0 :=
  ⟨List.sum_eq_zero fun v member => by
      obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
      simp [syncDebit, slot_noSync electra ok early replayed e inside],
    List.sum_eq_zero fun v member => by
      obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
      simp [syncCredit, slot_noSync electra ok early replayed e inside]⟩

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
    ∑ i ∈ keys, (events.map (syncDebit i)).sum ≤
      tail.blockCount * (preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope preset total) ∧
    ∑ i ∈ keys, ((events.map (syncCredit i)).sum + (events.map (syncDebit i)).sum) ≤
      tail.blockCount * (preset.SYNC_COMMITTEE_SIZE.toNat * syncSeatEnvelope preset total) := by
  induction tail generalizing events with
  | nil =>
    simp only [Run.balanceEvents, pure, Except.pure, Except.ok.injEq] at replayed
    subst replayed
    simp [Run.blockCount]
  | @snoc middle last pre step ih =>
    have earlyMiddle : middle.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have fuluMiddle : .fusaka ≤ middle.fork :=
      Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps)
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    obtain ⟨priorDebits, priorMoves⟩ := ih earlyMiddle priorOk
      (fun inner member => band inner (Run.Contains.earlier member step))
    split at rest
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
      obtain ⟨added, addedOk, rfl⟩ := rest
      have debitsSplit : ∑ i ∈ keys, ((prior ++ added).map (syncDebit i)).sum =
          ∑ i ∈ keys, (prior.map (syncDebit i)).sum +
            ∑ i ∈ keys, (added.map (syncDebit i)).sum := by
        simp only [List.map_append, List.sum_append, Finset.sum_add_distrib]
      rw [debitsSplit, sum_syncMoves_append]
      cases step with
      | slot ok =>
        have zero := slot_syncDebit_zero (Nat.le_trans (by decide) fuluMiddle) ok early addedOk
        simpa [fun i => (zero i).1, fun i => (zero i).2, Run.blockCount] using
          And.intro priorDebits priorMoves
      | @block fork before after engine signed due ok =>
        have altair : Fork.altair ≤ fork :=
          Nat.le_trans (show Fork.altair ≤ Fork.fusaka by decide) fuluMiddle
        have replay := Step.balanceEvents_block early addedOk
        obtain ⟨bound, boundMoves⟩ := block_syncDebits_le early altair replay total
          (fun T hT => band _ (Run.Contains.last pre _) T hT) keys
        simp only [Run.blockCount, Nat.add_mul, Nat.one_mul]
        exact ⟨by omega, by omega⟩
    · simp only [pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      cases step with
      | slot ok => simpa [Run.blockCount] using And.intro priorDebits priorMoves
      | block =>
        exact ⟨priorDebits.trans (Nat.mul_le_mul_right _ (Nat.le_succ _)),
          priorMoves.trans (Nat.mul_le_mul_right _ (Nat.le_succ _))⟩

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
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := Nat.pos_of_ne_zero empty
  have epochLe := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tail.chainSteps)
  rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat] at epochLe ⊢
  have low : x.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat * preset.SLOTS_PER_EPOCH.toNat ≤
      x.state.slot.toNat := Nat.div_mul_le_self _ _
  have high' := Nat.lt_mul_div_succ y.state.slot.toNat positive
  have blocks := tail.blocks_le_slots low (b := preset.SLOTS_PER_EPOCH.toNat *
      (y.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1) - 1) (by omega)
  have difference : (y.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 -
      x.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat) * preset.SLOTS_PER_EPOCH.toNat =
      preset.SLOTS_PER_EPOCH.toNat * (y.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1) -
        x.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat * preset.SLOTS_PER_EPOCH.toNat := by
    rw [Nat.sub_mul, Nat.mul_comm (preset.SLOTS_PER_EPOCH.toNat)]
  have grows : x.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat * preset.SLOTS_PER_EPOCH.toNat <
      preset.SLOTS_PER_EPOCH.toNat * (y.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1) := by
    calc x.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat * preset.SLOTS_PER_EPOCH.toNat
        ≤ y.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat * preset.SLOTS_PER_EPOCH.toNat :=
          Nat.mul_le_mul_right _ epochLe
      _ < preset.SLOTS_PER_EPOCH.toNat *
          (y.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1) := by
          rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm]
          omega
  have counted : tail.blockCount ≤ (y.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 -
      x.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat) * preset.SLOTS_PER_EPOCH.toNat := by
    rw [difference]
    generalize x.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat *
      preset.SLOTS_PER_EPOCH.toNat = lowest at *
    generalize preset.SLOTS_PER_EPOCH.toNat *
      (y.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1) = highest at *
    omega
  calc tail.blockCount * (preset.SYNC_COMMITTEE_SIZE.toNat * amount)
      ≤ ((y.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 -
        x.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat) * preset.SLOTS_PER_EPOCH.toNat) *
          (preset.SYNC_COMMITTEE_SIZE.toNat * amount) :=
        Nat.mul_le_mul_right _ counted
    _ = _ := by ring

/-- The sync debits of any set of keys over a run from Fulu fit one envelope per seat per slot.

The slots are those of the epochs that the run touches.

Every total along the run is within three halves of `total`.

Each block debits the keys at most one participant reward per seat.

Each block moves the keys at most one participant reward and its proposer share per seat. -/
private theorem Run.syncDebits_le {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (fulu : .fusaka ≤ x.fork) (early : y.fork < .glamsterdam) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (total : ℕ)
    (band : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → ∀ t : Gwei, getTotalActiveBalance w.state = .ok t →
        2 * t.toNat ≤ 3 * total)
    (keys : Finset ℕ) :
    ∑ i ∈ keys, (events.map (syncDebit i)).sum ≤
      ((getCurrentEpoch y.state).toNat + 1 - (getCurrentEpoch x.state).toNat) *
        preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
          syncEnvelope preset total ∧
    ∑ i ∈ keys, ((events.map (syncCredit i)).sum + (events.map (syncDebit i)).sum) ≤
      ((getCurrentEpoch y.state).toNat + 1 - (getCurrentEpoch x.state).toNat) *
        preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
          syncSeatEnvelope preset total := by
  have empty : preset.SLOTS_PER_EPOCH.toNat = 0 → syncEnvelope preset total = 0 := fun empty => by
    unfold syncEnvelope
    rw [empty]
    simp
  have bounds := run_syncDebits_le tail fulu early high replayed total band keys
  exact ⟨bounds.1.trans (Run.blockCount_mul_le tail _ empty),
    bounds.2.trans (Run.blockCount_mul_le tail _ fun e => by
      unfold syncSeatEnvelope
      simp [empty e])⟩
end PinSplit5

end GroupSeat

section GroupFloor

/-! ## PinSlashFloor -/

namespace PinSplit6

open Base Uint64 Models DirectSafety DirectSafety.Apriori.Internal

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

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
private def EpochFloorStatement (preset : Preset) (config : Config)
    (checks : SignatureChecks) : Prop :=
  ∀ {g m n : ForkedBeaconState preset} (_shared : Run config checks g m)
    (_genesis : Genesis (config := config) (checks := checks) g) (_caps : CapOrder preset)
    (_delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (_vector : 4 ≤ preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat)
    (_positive :
      0 < (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat)
    (r : Run config checks m n),
    .fusaka ≤ m.fork → n.fork < .glamsterdam →
    (getCurrentEpoch n.state = getCurrentEpoch m.state ∨
      ∃ (z : ForkedBeaconState preset) (pre : Run config checks m z)
        (ok : advanceSlotAcross config checks z = .ok n),
        r = pre.snoc (Step.slot ok) ∧ getCurrentEpoch z.state = getCurrentEpoch m.state ∧
          (getCurrentEpoch n.state).toNat = (getCurrentEpoch m.state).toNat + 1) →
    ∀ (i : ℕ) (val : Validator), m.state.validators.data[i]? = some val →
    val.activationEpoch ≠ FAR_FUTURE_EPOCH →
    (∀ w, n.state.validators.data[i]? = some w →
      (getCurrentEpoch m.state).toNat + 1 < w.exitEpoch.toNat) →
    (val.slashed = true → (getCurrentEpoch n.state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 < val.withdrawableEpoch.toNat) →
    ∀ C : ℕ, C ≤ (withdrawalMaxEffectiveBalance preset m.fork val).toNat →
    ∀ {events : List (BalanceEvent preset)},
      r.balanceEvents (getCurrentEpoch m.state).toNat = .ok events →
    ∃ (z : ForkedBeaconState preset) (pre : Run config checks m z) (post : Run config checks z n),
      r = pre.append post ∧ getCurrentEpoch z.state = getCurrentEpoch m.state ∧
      min (actualBalanceAt m i) C ≤ actualBalanceAt n i +
        (if getCurrentEpoch m.state < getCurrentEpoch n.state ∧
            ∃ total, getTotalActiveBalance z.state = .ok total then
          passPenaltyRate config z i else 0) +
        (events.map (syncDebit i)).sum + (events.map (floorPartialDebit i.toUInt64)).sum +
        (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
          then effectiveAt m i /
            (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat
          else 0)

/-- Every fork from Fulu on has the slashing quotient of Electra. -/
private theorem mspq_fusaka {f : Fork} (h : .fusaka ≤ f) :
    (EthLib.Consensus.parameters preset f).MIN_SLASHING_PENALTY_QUOTIENT =
      (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT := by
  have pectra : .pectra ≤ f := Nat.le_trans (by decide) h
  have pectra' : .pectra ≤ Fork.fusaka := by decide
  simp [EthLib.Consensus.parameters, ge_iff_le, pectra, pectra']


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
      if ∃ total, getTotalActiveBalance z.state = .ok total then passPenaltyRate config z i
      else 0 := by
  have starts : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      (pre.snoc (Step.slot ok)).Contains step →
        getCurrentEpoch u.state = getCurrentEpoch m.state := by
    intro u w step member
    cases member with
    | last => exact same
    | earlier member _ =>
      obtain ⟨before, after, -⟩ := pre.contains_split step member
      exact UInt64.le_antisymm
        (same ▸ currentEpoch_le_of_chainSteps ((Run.nil.snoc step).append after).chainSteps)
        (currentEpoch_le_of_chainSteps before.chainSteps)
  have bound := segment_passDebit_le_guarded (pre.snoc (Step.slot ok)) early altair
    (getCurrentEpoch m.state).toNat endEpoch starts inside
    (if ∃ total, getTotalActiveBalance z.state = .ok total then passPenaltyRate config z i
      else 0)
    (fun {z'} pre' ok' split before found => by
      cases split
      simp [found])
    replayed
  rwa [ite_eq_left (by rw [same] at crossed; exact UInt64.lt_iff_toNat_lt.mpr crossed)] at bound

open Classical in
/-- The floor of one epoch of a key, through any slashing of the key. -/
private theorem epochFloor : EpochFloorStatement preset config checks := by
  intro g m n shared genesis caps delay vector positive r hm hn shape i val hval hact hexit hslash
    C hC events replayed
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
    have lo := currentEpoch_le_of_chainSteps pre'.chainSteps
    have hi := currentEpoch_le_of_chainSteps ((Run.nil.snoc step).append post).chainSteps
    have forkLo := fork_le_of_chainSteps pre'.chainSteps
    have forkHi := fork_le_of_chainSteps post.chainSteps
    refine ⟨?_, Nat.le_trans hm forkLo, Nat.lt_of_le_of_lt forkHi hn⟩
    have member : r.Contains step := by
      rw [← split, Run.contains_append]
      exact .inl (.last _ _)
    rcases shape with same | ⟨z, pre, ok, req, hz, h1⟩
    · exact UInt64.le_antisymm (same ▸ hi) lo
    · subst req
      cases member with
      | last => exact hz
      | earlier member _ =>
        obtain ⟨_, q, _⟩ := pre.contains_split step member
        exact UInt64.le_antisymm
          (hz ▸ currentEpoch_le_of_chainSteps ((Run.nil.snoc step).append q).chainSteps) lo
  obtain ⟨z, pre, post, hsplit, hz, hpen⟩ : ∃ (z : ForkedBeaconState preset)
      (pre : Run config checks m z) (post : Run config checks z n),
      r = pre.append post ∧ getCurrentEpoch z.state = getCurrentEpoch m.state ∧
      (events.map (penaltyDebit iv.toNat)).sum ≤
        (if getCurrentEpoch m.state < getCurrentEpoch n.state ∧
            ∃ total, getTotalActiveBalance z.state = .ok total then
          passPenaltyRate config z iv.toNat else 0) := by
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
      (getCurrentEpoch m.state).toNat endEpoch iv val hval hact
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
        refine ⟨?_, ⟨fun _ => by omega, fun slashed => ?_⟩, ?_,
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
      (events.map (penaltyDebit iv.toNat)).sum + (events.map (syncDebit iv.toNat)).sum := by
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
end PinSplit6

end GroupFloor

section GroupNewKey

/-! ## PinExitQueue: the effective balance of a new key -/

namespace PinSplit

open Base Uint64 Models DirectSafety PinSplit2 PinSplit6

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
  set C := min b' cap with hC
  have hEB : EB ≤ C + band := by
    rcases le_total b' cap with h | h
    · have : C = b' := min_eq_left h
      omega
    · have : C = cap := min_eq_right h
      omega
  have hcle : min b' K ≤ C := by
    apply le_min (min_le_left _ _)
    exact (min_le_right _ _).trans hcap
  -- the key's balance after the epoch, scaled
  have bound : C * φt ≤ b * φt + (C + band) * (pen + 1) + X * φt := by
    have h1 : C * φt ≤ (b + pass + X) * φt := Nat.mul_le_mul_right _ seg
    have h2 : pass * φt ≤ (C + band) * (pen + 1) :=
      pr.trans (Nat.mul_le_mul_right _ hEB)
    nlinarith
  by_cases big : K ≤ b
  · have : min b K = K := min_eq_right big
    rw [this]
    have : min b' K ≤ K := min_le_right _ _
    have : φt1 ≤ φt := by omega
    nlinarith
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
    set C := min b' cap with hC
    have hEB : EB ≤ C + band := by
      rcases le_total b' cap with h | h
      · have : C = b' := min_eq_left h
        omega
      · have : C = cap := min_eq_right h
        omega
    have hcle : min b' K ≤ C := le_min (min_le_left _ _) ((min_le_right _ _).trans hcap)
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
      · have : min b K = K := min_eq_right big
        rw [this]
        have : min b' K ≤ K := min_le_right _ _
        have : φt1 ≤ φt := by omega
        nlinarith
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

/-- One step of a chain moves the current epoch on by at most one. -/
private theorem ChainStep.epoch_le_succ {a b : ForkedBeaconState preset}
    (step : ChainStep config checks a b) :
    (getCurrentEpoch b.state).toNat ≤ (getCurrentEpoch a.state).toNat + 1 := by
  cases step with
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    have kept := processUpgrades_slot upgrades
    have next := advanceSlot_slot slotOk
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
    simp only at kept next ⊢
    rw [kept, next]
    by_cases zero : preset.SLOTS_PER_EPOCH.toNat = 0
    · simp [zero]
    · have positive : 1 ≤ preset.SLOTS_PER_EPOCH.toNat := Nat.pos_of_ne_zero zero
      calc (a.state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat
          ≤ (a.state.slot.toNat + preset.SLOTS_PER_EPOCH.toNat) /
              preset.SLOTS_PER_EPOCH.toNat :=
            Nat.div_le_div_right (Nat.add_le_add_left positive _)
        _ = a.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 :=
            Nat.add_div_right _ positive
  | block engine signed validate ok =>
    have same := processBlock_slot (applySignedBlock_ok ok).2.1
    simp only [getCurrentEpoch, same]
    exact Nat.le_succ _

/-- A run from an epoch to a later one has a slot step that leaves a given epoch between them. -/
private theorem Run.cross_split {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (k : ℕ) (low : (getCurrentEpoch x.state).toNat ≤ k)
    (high : k < (getCurrentEpoch y.state).toNat) :
    ∃ (z n : ForkedBeaconState preset) (pre : Run config checks x z)
      (ok : advanceSlotAcross config checks z = .ok n) (rest : Run config checks n y),
      tail = (pre.snoc (Step.slot ok)).append rest ∧ (getCurrentEpoch z.state).toNat = k ∧
        (getCurrentEpoch n.state).toNat = k + 1 := by
  obtain ⟨m, n, pre, step, post, split, hm, hn⟩ :=
    Run.split_at_flip tail (fun z => k < (getCurrentEpoch z.state).toNat) (by omega) high
  have missing : ¬k < (getCurrentEpoch m.state).toNat := hm
  have gained : k < (getCurrentEpoch n.state).toNat := hn
  have bound := ChainStep.epoch_le_succ step.chainStep
  cases step with
  | slot ok => exact ⟨m, n, pre, ok, post, split, by omega, by omega⟩
  | @block fork before after engine signed due ok =>
    have same := processBlock_slot (applySignedBlock_ok ok).2.1
    have e : (getCurrentEpoch after).toNat = (getCurrentEpoch before).toNat := by
      simp only [getCurrentEpoch, same]
    simp only at missing gained
    omega

/-- A run that starts at or before an epoch and ends at or after it passes a state of that epoch. -/
private theorem Run.exists_epoch_split {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (k : ℕ)
    (low : (getCurrentEpoch x.state).toNat ≤ k) (high : k ≤ (getCurrentEpoch y.state).toNat) :
    ∃ (z : ForkedBeaconState preset) (pre : Run config checks x z) (post : Run config checks z y),
      (getCurrentEpoch z.state).toNat = k ∧ tail = pre.append post := by
  by_cases last : k = (getCurrentEpoch y.state).toNat
  · exact ⟨y, tail, .nil, last.symm, rfl⟩
  · obtain ⟨z, n, pre, ok, rest, split, hz, -⟩ := Run.cross_split tail k low (by omega)
    exact ⟨z, pre, (Run.nil.snoc (Step.slot ok)).append rest, hz, by
      rw [split, Run.append_assoc]; rfl⟩

/-- A key that is active at the end of a run is scheduled two epochs before its activation.

It is not active by the epoch after the start of the run.

At the state `z` that the run reaches in that epoch, the key holds its activation epoch `A`.

Activity up to `A` is fixed at `z`, since the seed lookahead is at least three epochs. -/
private theorem Run.start_state {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (window : preset.SeedLookaheadAtLeastThree) (i : ℕ)
    (pending : ∀ v, x.state.validators.data[i]? = some v →
      (getCurrentEpoch x.state).toNat + 1 < v.activationEpoch.toNat)
    (active : isActiveAt y.state (getCurrentEpoch y.state) i = true) :
    ∃ (z : ForkedBeaconState preset) (pre : Run config checks x z) (post : Run config checks z y)
      (v0 vy : Validator), tail = pre.append post ∧ z.state.validators.data[i]? = some v0 ∧
      y.state.validators.data[i]? = some vy ∧ v0.activationEpoch = vy.activationEpoch ∧
      (getCurrentEpoch z.state).toNat + 2 = vy.activationEpoch.toNat ∧
      vy.activationEpoch.toNat ≤ (getCurrentEpoch y.state).toNat ∧
      (getCurrentEpoch y.state).toNat < vy.exitEpoch.toNat := by
  obtain ⟨vy, foundY, activeY⟩ := isActiveAt_eq_true_iff.mp active
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at activeY
  have lowY := UInt64.le_iff_toNat_le.mp activeY.1
  have highY := UInt64.lt_iff_toNat_lt.mp activeY.2
  have exitBound := vy.exitEpoch.toNat_lt
  have fixedWindow := window.lookahead
  -- Activity at the epoch `A` of the key, as the end state reads it.
  have activeAtA : isActiveAt y.state vy.activationEpoch i = true := by
    refine isActiveAt_eq_true_iff.mpr ⟨vy, foundY, ?_⟩
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨UInt64.le_refl _, UInt64.lt_iff_toNat_lt.mpr (by omega)⟩
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
    by omega, lowY, highY⟩

/-! ## Hypothesis of the new key's floor -/

/-- Right after a slot step that moves the epoch on, the effective balances lie within the bands.

The step ran the epoch transition, and its upgrades keep the bands. -/
private def EpochStartHysteresis (preset : Preset) (config : Config)
    (checks : SignatureChecks) : Prop :=
  ∀ {a b : ForkedBeaconState preset} (_step : Step config checks a b),
    getCurrentEpoch a.state < getCurrentEpoch b.state → Hysteresis b.state

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
    passPenaltyRate config z i * stakeFloorAt config x high t ≤
      effectiveAt z i *
        (stakeFloorAt config x high t - stakeFloorAt config x high (t + 1) + 1) := by
  have succ := floor_succ (config := config) x high t
  have eq : stakeFloorAt config x high t = stakeFloorAt config x high (t + 1) +
      epochPenalty preset config (startInactivityScore config x)
        (stakeCeilingAt config x high t + slashedUnwithdrawnStake x)
        (stakeFloorAt config x high t) t := by
    omega
  have pen : stakeFloorAt config x high t - stakeFloorAt config x high (t + 1) =
      epochPenalty preset config (startInactivityScore config x)
        (stakeCeilingAt config x high t + slashedUnwithdrawnStake x)
        (stakeFloorAt config x high t) t := by omega
  rw [pen]
  have totalValue := getTotalActiveBalance_toNat totalOk
  unfold activeBalanceTotal at totalValue
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
  unfold passPenaltyRate epochPenalty
  dsimp only
  rw [totalValue] at first
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
    set C := min b' cap with hC
    have hEB : EB ≤ C + band := by
      rcases le_total b' cap with h | h
      · have : C = b' := min_eq_left h
        omega
      · have : C = cap := min_eq_right h
        omega
    by_cases cK : C ≤ K
    · have hcle : min b' K ≤ C := le_min (min_le_left _ _) ((min_le_right _ _).trans hcap)
      have slB : sl ≤ Bq := by
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

They also hold the preset facts, and the statements that the floor takes as hypotheses. -/
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
  hysteresis : EpochStartHysteresis preset config checks

/-- The total active balance of a state of a run lies between the floor and the ceiling.

It is `total_within_guard` (PinDriftBound, private) at the index of the state. -/
private theorem Ctx.total_bounds {g x z : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (run : Run config checks x z) (early : z.fork < .glamsterdam)
    (within : (getCurrentEpoch z.state).toNat ≤ high + 1) {total : Gwei}
    (totalOk : getTotalActiveBalance z.state = .ok total) :
    stakeFloorAt config x high (ix x z) ≤ total.toNat ∧
      total.toNat ≤ stakeCeilingAt config x high (ix x z) := by
  obtain ⟨ceiling, -, floor⟩ := ceilingFloor_electra c.shared run high
    ⟨c.genesis, c.parameters, c.caps, c.aligned, early, within, c.guard⟩ c.twoSlots c.electra
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps run.chainSteps) early
  have unit := (ceiling_unit_of_guard c.shared c.genesis c.aligned xEarly c.electra c.guard).trans
    (stakeCeilingAt_mono c.electra (Nat.zero_le (ix x z)))
  refine ⟨floor total totalOk, ?_⟩
  obtain ⟨-, -, value⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok totalOk)
  rw [value]
  exact max_le unit ceiling

/-- Along the window, the floor stays within three halves of its start.

The start floor is below the stake at the start, which the funded stake covers.

The funded stake is below the first ceiling, which is below the last.

The guard asks that twice the last ceiling be at most three times the last floor. -/
private theorem Ctx.ratio {g x : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (early : x.fork < .glamsterdam) {s : ℕ}
    (inside : s ≤ high + 1 - (getCurrentEpoch x.state).toNat)
    (within : (getCurrentEpoch x.state).toNat ≤ high + 1) :
    2 * stakeFloorAt config x high 0 ≤ 3 * stakeFloorAt config x high s := by
  have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge c.electra
  have zero : preElectraEpochs config x high = 0 := by simp [preElectraEpochs, notBefore]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ratioGuard, -⟩ := id c.guard
  rw [zero] at ratioGuard
  have ratio := ratioGuard (high + 1 - (getCurrentEpoch x.state).toNat) (Nat.zero_le _)
    (by unfold driftHorizon; omega)
  have first : stakeFloorAt config x high 0 ≤ stakeCeilingAt config x high 0 :=
    (floor_initial_le_reference x high).trans
      ((funding_active_le x early (c.shared.pubkeysDistinct c.genesis)).trans
        (funded_le_ceiling_initial c.electra))
  have anti : stakeFloorAt config x high (high + 1 - (getCurrentEpoch x.state).toNat) ≤
      stakeFloorAt config x high s := stakeFloorAt_anti inside
  have mono : stakeCeilingAt config x high 0 ≤
      stakeCeilingAt config x high (high + 1 - (getCurrentEpoch x.state).toNat) :=
    stakeCeilingAt_mono c.electra (Nat.zero_le _)
  have ratio' : 2 * stakeCeilingAt config x high (high + 1 - (getCurrentEpoch x.state).toNat) ≤
      3 * stakeFloorAt config x high (high + 1 - (getCurrentEpoch x.state).toNat) := by
    simpa [stakeCeilingAt, stakeFloorAt, zero] using ratio
  omega

/-- The debits of key `i` in a list of events: its sync debits and its partial payments. -/
private def keyDebits (i : ℕ) (events : List (BalanceEvent preset)) : ℕ :=
  (events.map (syncDebit i)).sum + (events.map (floorPartialDebit i.toUInt64)).sum

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

/-- The rounded-up quotient `Bq` covers its numerator. -/
private theorem ceil_div_cover (a Q : ℕ) (positive : 0 < Q) : a ≤ Q * ((a + Q - 1) / Q) := by
  have h1 := Nat.div_add_mod (a + Q - 1) Q
  have h2 := Nat.mod_lt (a + Q - 1) positive
  omega

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
        ((events.map (syncDebit i)).sum + (events.map (floorPartialDebit i.toUInt64)).sum +
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
  have capLe : preset.MAX_EFFECTIVE_BALANCE.toNat ≤
      (withdrawalMaxEffectiveBalance preset m.fork val).toNat :=
    UInt64.le_iff_toNat_le.mp (Internal.minimum_cap c.caps.activation c.caps.compounding val)
  have positiveQ :
      0 < (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat := by
    have := c.quotientTwo
    omega
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
          passPenaltyRate config z' i else 0) *
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
      have bounds := c.total_bounds z'x z'Early (by omega) totalOk
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
  have hB : K + band ≤ Q * Bq := ceil_div_cover _ _ positiveQ
  have hanti : stakeFloorAt config x high (t + 1) ≤ stakeFloorAt config x high t :=
    stakeFloorAt_anti (Nat.le_succ t)
  have hzero : stakeFloorAt config x high t ≤ stakeFloorAt config x high 0 :=
    stakeFloorAt_anti (Nat.zero_le t)
  have nWithin := step
  have cxIn : (getCurrentEpoch x.state).toNat ≤ high + 1 := by omega
  have xEarly : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Nat.le_trans hxm (Nat.le_trans mz zn)) early
  have ratio := c.ratio xEarly (s := t + 1) (by omega) cxIn
  have roomT := c.room
  have hφ : 6 * Q ≤ stakeFloorAt config x high (t + 1) := by
    have := c.big
    omega
  have hband' : 2 * stakeFloorAt config x high t ≤ 3 * stakeFloorAt config x high (t + 1) := by
    omega
  have capEB : effectiveAt m i ≤ (withdrawalMaxEffectiveBalance preset m.fork val).toNat := by
    have := Run.effectiveBalance_capped shared' c.genesis c.caps.activation c.caps.compounding
      mEarly val (Array.mem_of_getElem? found)
    have e : effectiveAt m i = val.effectiveBalance.toNat := by simp [effectiveAt, found]
    rw [e]
    exact UInt64.le_iff_toNat_le.mp this
  have bound := step_arith_slash (actualBalanceAt m i) (actualBalanceAt n i)
    (withdrawalMaxEffectiveBalance preset m.fork val).toNat K band
    (if getCurrentEpoch m.state < getCurrentEpoch n.state ∧
        ∃ total, getTotalActiveBalance z'.state = .ok total then passPenaltyRate config z' i else 0)
    ((events.map (syncDebit i)).sum + (events.map (floorPartialDebit i.toUInt64)).sum)
    (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
      then effectiveAt m i / Q else 0)
    Q Bq (stakeFloorAt config x high t) (stakeFloorAt config x high (t + 1))
    (stakeFloorAt config x high t - stakeFloorAt config x high (t + 1)) (effectiveAt m i)
    capLe c.quotientTwo hB (by omega)
    (by split <;> [exact Nat.mul_div_le _ _; simp])
    hyst capEB pass (by omega) hφ hband'
  have charge : (if (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧
        w.slashed = true then effectiveAt m i / Q else 0) = 0 then 0 else Bq) ≤
      (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
        then Bq else 0) := by
    by_cases h : val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧
      w.slashed = true
    · rw [ite_eq_left h, ite_eq_left h]
      by_cases e : effectiveAt m i / Q = 0 <;> simp [e]
    · rw [ite_eq_right h, ite_eq_right h]
      simp
  have mul := Nat.mul_le_mul_right (stakeFloorAt config x high t)
    (Nat.add_le_add_left charge ((events.map (syncDebit i)).sum +
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
      ((events.map (syncDebit i)).sum + (events.map (floorPartialDebit i.toUInt64)).sum +
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
  have capLe : preset.MAX_EFFECTIVE_BALANCE.toNat ≤
      (withdrawalMaxEffectiveBalance preset m.fork val).toNat :=
    UInt64.le_iff_toNat_le.mp (Internal.minimum_cap c.caps.activation c.caps.compounding val)
  have positiveQ :
      0 < (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat := by
    have := c.quotientTwo
    omega
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
  have hB : K + band ≤ Q * Bq := ceil_div_cover _ _ positiveQ
  have capEB : effectiveAt m i ≤ (withdrawalMaxEffectiveBalance preset m.fork val).toNat := by
    have := Run.effectiveBalance_capped shared' c.genesis c.caps.activation c.caps.compounding
      mEarly val (Array.mem_of_getElem? found)
    have e : effectiveAt m i = val.effectiveBalance.toNat := by simp [effectiveAt, found]
    rw [e]
    exact UInt64.le_iff_toNat_le.mp this
  have bound := same_arith (actualBalanceAt m i) (actualBalanceAt n i)
    (withdrawalMaxEffectiveBalance preset m.fork val).toNat K band
    ((events.map (syncDebit i)).sum + (events.map (floorPartialDebit i.toUInt64)).sum)
    (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
      then effectiveAt m i / Q else 0)
    Q Bq (effectiveAt m i) capLe c.quotientTwo hB (by omega)
    (by split <;> [exact Nat.mul_div_le _ _; simp]) hyst capEB
  have charge : (if (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧
        w.slashed = true then effectiveAt m i / Q else 0) = 0 then 0 else Bq) ≤
      (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
        then Bq else 0) := by
    by_cases h : val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧
      w.slashed = true
    · rw [ite_eq_left h, ite_eq_left h]
      by_cases e : effectiveAt m i / Q = 0 <;> simp [e]
    · rw [ite_eq_right h, ite_eq_right h]
      simp
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
    stakeFloorAt_anti (Nat.le_succ _)
  have hzero : stakeFloorAt config x high
      ((getCurrentEpoch z.state).toNat - (getCurrentEpoch x.state).toNat) ≤
        stakeFloorAt config x high 0 := stakeFloorAt_anti (Nat.zero_le _)
  have ratio := c.ratio xEarly (s := (getCurrentEpoch m.state).toNat -
    (getCurrentEpoch x.state).toNat) (by omega) cxIn
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
  exact ⟨claim', Ctx.hyst_start c (hz.append (rm.append (ins.snoc (Step.slot ok))))
    (c.hysteresis (Step.slot ok) lt) found'⟩

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
  have ratio0 := c.ratio xEarly (s := cz - (getCurrentEpoch x.state).toNat) (by omega) cxIn
  have ratioK := c.ratio xEarly (s := ck - (getCurrentEpoch x.state).toNat) (by omega) cxIn
  have hzero : stakeFloorAt config x high (cz - (getCurrentEpoch x.state).toNat) ≤
      stakeFloorAt config x high 0 := stakeFloorAt_anti (Nat.zero_le _)
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

/-- A state on the balance path of a run is a state of the run, or the state inside a slot step.

The state inside a slot step comes after the slot and its epoch transition, before the upgrades. -/
private theorem Run.mem_balancePath_split {z w : ForkedBeaconState preset}
    (r : Run config checks z w) {p : ForkedBeaconState preset} (member : p ∈ r.balancePath) :
    (∃ (rp : Run config checks z p) (rest : Run config checks p w), r = rp.append rest) ∨
    (∃ (q n : ForkedBeaconState preset) (rq : Run config checks z q)
      (ok : advanceSlotAcross config checks q = .ok n) (rest : Run config checks n w)
      (adv : BeaconState preset q.fork), r = (rq.snoc (Step.slot ok)).append rest ∧
        advanceSlot config checks q.state = .ok adv ∧ p = ⟨q.fork, adv⟩ ∧
        processUpgrades config checks ⟨q.fork, adv⟩ = .ok n) := by
  induction r with
  | nil =>
    simp only [Run.balancePath, List.mem_singleton] at member
    subst member
    exact .inl ⟨.nil, .nil, rfl⟩
  | @snoc q last pre step ih =>
    simp only [Run.balancePath, List.mem_append] at member
    rcases member with member | member
    · rcases ih member with ⟨rp, rest, eq⟩ | ⟨q', n, rq, ok, rest, adv, eq, adv_ok, hp, up⟩
      · exact .inl ⟨rp, rest.snoc step, by rw [eq]; rfl⟩
      · exact .inr ⟨q', n, rq, ok, rest.snoc step, adv, by rw [eq]; rfl, adv_ok, hp, up⟩
    · cases step with
      | block engine signed due ok =>
        simp only [Step.balancePath, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact .inl ⟨pre, (Run.nil.snoc (.block engine signed due ok)), rfl⟩
        · exact .inl ⟨pre.snoc (.block engine signed due ok), .nil, rfl⟩
      | slot ok =>
        have unfold_ok := ok
        obtain ⟨adv, advOk, upgrades⟩ := bind_ok_iff.mp unfold_ok
        simp only [Step.balancePath, advOk, Except.toOption, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl | rfl
        · exact .inl ⟨pre, (Run.nil.snoc (.slot ok)), rfl⟩
        · exact .inr ⟨_, last, pre, ok, .nil, adv, rfl, advOk, rfl, upgrades⟩
        · exact .inl ⟨pre.snoc (.slot ok), .nil, rfl⟩

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

/-! ## C3: the effective balance of a new key -/

open DirectSafety.Apriori.Internal in
/-- C3: a key created on the run keeps its effective balance near two thirds of the maximum.

Under the guard at the split, the key's effective balance at the end of the window is large.

It is at least two thirds of `MAX_EFFECTIVE_BALANCE`.

The bound loses the initial slashing penalty, the downward band and an increment.

The key's sync debits and its partial payments are added back.

The key is scheduled at the split.

It is not active by the epoch after the split, and it is active at the end.

The proof follows the key from two epochs before its activation.

There it holds the maximum effective balance.

It follows the key to the first state of the last epoch.

Its potential is the least of its balance and the maximum, plus the band.

The potential keeps the fraction of the floor path that the floor path keeps.

It loses a rounding error, which the room covers.

The effective balance follows from the balance by hysteresis. -/
private theorem Run.new_key_effective_floor {g x y : ForkedBeaconState preset}
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
    (hysteresis : EpochStartHysteresis preset config checks)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
        preset.MAX_EFFECTIVE_BALANCE.toNat /
          (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        preset.downwardBand - preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      effectiveAt y i + (events.map (syncDebit i)).sum +
        (events.map (floorPartialDebit i.toUInt64)).sum := by
  classical
  obtain ⟨z, pre, post, v0, vy, split, found0, foundY, sameAct, actEq, actLe, exitGt⟩ :=
    Run.start_state tail window i pending active
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
  have finite : getCurrentEpoch z.state < FAR_FUTURE_EPOCH :=
    UInt64.lt_iff_toNat_lt.mpr (by omega)
  have plusOne : (getCurrentEpoch z.state + 1).toNat = (getCurrentEpoch z.state).toNat + 1 := by
    rw [UInt64.toNat_add]
    have : (1 : UInt64).toNat = 1 := rfl
    rw [this]
    exact Nat.mod_eq_of_lt (by omega)
  have lessAct : getCurrentEpoch z.state + 1 < v0.activationEpoch :=
    UInt64.lt_iff_toNat_lt.mpr (by rw [plusOne, sameAct]; omega)
  obtain ⟨funded, maxLe, unslashed⟩ := (Internal.run_eligible_balance (shared.append pre) genesis
    caps.activation caps.compounding aligned zEarly finite).2 electraZ i v0 found0
    (Or.inl actNeFar)
    (UInt64.lt_iff_toNat_lt.mpr (by have := UInt64.lt_iff_toNat_lt.mp lessAct; omega))
  obtain ⟨bal, hbal, effLe⟩ := funded (by
    have := UInt64.lt_iff_toNat_lt.mp lessAct
    omega)
  have bal0 : preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt z i := by
    have := UInt64.le_iff_toNat_le.mp (UInt64.le_trans maxLe effLe)
    simpa [actualBalanceAt, hbal] using this
  have hystZ : effectiveAt z i ≤ actualBalanceAt z i + preset.downwardBand := by
    have := UInt64.le_iff_toNat_le.mp effLe
    simp only [effectiveAt, actualBalanceAt, found0, hbal, Option.map_some, Option.getD_some]
    omega
  have effZ : preset.MAX_EFFECTIVE_BALANCE.toNat ≤ effectiveAt z i := by
    have := UInt64.le_iff_toNat_le.mp maxLe
    simpa [effectiveAt, found0] using this
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
  have room := room_of_guard shared genesis aligned (Nat.lt_of_le_of_lt
    (fork_le_of_chainSteps tail.chainSteps) early) electra guard facts
  have big := big_of_guard shared genesis aligned (Nat.lt_of_le_of_lt
    (fork_le_of_chainSteps tail.chainSteps) early) electra guard facts
  have c : Ctx config checks g x high :=
    { shared := shared, genesis := genesis, parameters := parameters, caps := caps,
      aligned := aligned, twoSlots := twoSlots, electra := electra, fulu := fulu, guard := guard,
      delay := delay, vector := facts.vector, big := big, factor := facts.reward,
      quotientTwo := facts.quotient, margin := facts.margin, room := room,
      hysteresis := hysteresis }
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
  have hBal := Run.effective_floor_of_balance_floor (pre0.snoc (Step.slot ok)) nEarly fuluZ bands i
    nIn
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
      simpa [capAt, found] using this)
  have sameEff : effectiveAt y i = effectiveAt n i := by
    have inside : i < n.state.validators.data.size := by
      obtain ⟨val, found, -⟩ := (pre0.snoc (Step.slot ok)).registryLifecycle.validators i v0 found0
      exact (Array.getElem?_eq_some_iff.mp found).1
    exact run_same_epoch_effective rest0 early (UInt64.toNat_inj.mp (by omega)) i inside
  rw [sameEff]
  have kd : keyDebits i events = (events.map (syncDebit i)).sum +
      (events.map (floorPartialDebit i.toUInt64)).sum := rfl
  have fin := final_floor
    (2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
        preset.MAX_EFFECTIVE_BALANCE.toNat /
          (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        preset.downwardBand) preset.EFFECTIVE_BALANCE_INCREMENT.toNat (keyDebits i events)
    (effectiveAt z i) (effectiveAt n i) preset.MAX_EFFECTIVE_BALANCE.toNat
    ((Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (by omega))) effZ hBal
  omega

end PinSplit

end GroupNewKey

end EthLib.Consensus.Models.Network
