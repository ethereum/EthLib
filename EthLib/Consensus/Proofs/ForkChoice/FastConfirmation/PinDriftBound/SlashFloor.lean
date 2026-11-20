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
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound.Band

@[expose] public section

namespace EthLib.Consensus.Models.Network

open DirectSafety.Apriori.Internal (recordBalance_single)

section

/-! ## PinSlashFloor -/

namespace PinSlashFloor

open Base Uint64 Models DirectSafety DirectSafety.Apriori.Internal

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- Every fork from Fulu on has the slashing quotient of Electra. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.mspq_fusaka {f : Fork} (h : .fusaka
  ≤ f) :
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
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.epochFloor {g m n :
  ForkedBeaconState preset} (shared : Run config checks g m)
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
    rw [PinDrift.Internal.mspq_fusaka hm]; exact positive
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
        · rw [PinDrift.Internal.mspq_fusaka hm, PinDrift.Internal.mspq_fusaka fusaka]
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

end EthLib.Consensus.Models.Network
