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
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound.Keys

@[expose] public section

namespace EthLib.Consensus.Models.Network

open DirectSafety.Apriori.Internal (recordBalance_single)

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
  rcases PinDrift.Internal.mem_or_source_of_append events rfl member with old | new
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
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.blockReplay_sync_split {fork :
  Fork} {a t : BeaconState preset fork}
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
    PinDrift.Internal.blockReplay_sync_split early altair replay
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
  have unconditional := PinDrift.Internal.blockReplay_unconditional electra early engine u
    signed.message
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

end EthLib.Consensus.Models.Network
