module

public import EthLib.Consensus.Proofs.Transition.Operations
public import EthLib.Consensus.Transition.EpochPending

/-!
# Proofs: the pending deposits of an epoch

The pending deposits of an epoch keep one balance for each validator.

The queue never grows.

A pass never credits more inside the churn than the churn available.

A pass reads a prefix of the queue, applies some of it in order, and postpones the others.

So the queue splits into the deposits added to the balances, those dropped, and the queue after.

The balances plus the amounts in the queue never rise.

The pass of an epoch reads only deposits with a slot at most the first slot of the finalized epoch.

In Electra, while deposits of the old mechanism remain, it reads no request either.

So only such deposits leave the queue.

From Gloas, the churn of deposits is the churn of activations alone.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- A pass over the pending deposits keeps one balance for each validator. -/
theorem balancesMatch_passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      BalancesMatch state → BalancesMatch pass.1.state
  | [], _, _, _, _, _, computed, holds => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact holds
  | deposit :: rest, state, processed, count, postponed, pass, computed, holds => by
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      exact holds
    split at computed
    · split at computed
      · cases computed
      rename_i credited
      split at computed
      · cases computed
      cases computed
      exact balancesMatch_passPendingDeposits (deposits := rest) ‹_›
        ((applyPendingDeposit_kept credited).1 holds)
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact balancesMatch_passPendingDeposits (deposits := rest) ‹_› holds
    split at computed
    · cases computed
    split at computed
    · cases computed
      exact holds
    split at computed
    · cases computed
    rename_i credited
    split at computed
    · cases computed
    cases computed
    exact balancesMatch_passPendingDeposits (deposits := rest) ‹_›
      ((applyPendingDeposit_kept credited).1 holds)

/-- A pass that starts within the churn available credits no more than that churn inside it. -/
theorem passPendingDeposits_processed_le {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      processed ≤ available → pass.1.processed ≤ available
  | [], _, _, _, _, _, computed, within => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact within
  | deposit :: rest, state, processed, count, postponed, pass, computed, within => by
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      exact within
    split at computed
    · split at computed
      · cases computed
      split at computed
      · cases computed
      cases computed
      exact passPendingDeposits_processed_le (deposits := rest) ‹_› within
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact passPendingDeposits_processed_le (deposits := rest) ‹_› within
    split at computed
    · cases computed
    split at computed
    · cases computed
      exact within
    rename_i fits
    split at computed
    · cases computed
    split at computed
    · cases computed
    cases computed
    exact passPendingDeposits_processed_le (deposits := rest) ‹_›
      (UInt64.not_lt.mp fits)

/-- The pending deposits of an epoch end with a pass over the queue from its front.

The pass reads the next epoch and the churn available.

That churn is the churn left from the last epoch and the churn of deposits.

It stops at a deposit that waits for the first slot of the finalized epoch.

The registry and the balances are those of the pass.

The queue holds the deposits that the pass did not reach, then those it postponed. -/
theorem processPendingDeposits_pass {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    ∃ nextEpoch churn available finalizedSlot pass,
      liftArith (addChecked (getCurrentEpoch state) 1) = .ok nextEpoch ∧
      depositChurnLimit config state = .ok churn ∧
      liftArith (addChecked (state.depositBalanceToConsume electra) churn) = .ok available ∧
      liftArith (computeStartSlotAtEpoch preset state.finalizedCheckpoint.epoch) =
        .ok finalizedSlot ∧
      passPendingDeposits config checks (depositWaits state finalizedSlot) nextEpoch available
          state 0 0 #[] (state.pendingDeposits electra).data.toList = .ok pass ∧
        after.validators = pass.1.state.validators ∧ after.balances = pass.1.state.balances ∧
        (after.pendingDeposits electra).data = pass.1.rest.toArray ++ pass.1.postponed := by
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals exact ⟨_, _, _, _, _, liftAccessor_ok.mp ‹_›, liftAccessor_ok.mp ‹_›,
    liftAccessor_ok.mp ‹_›, liftAccessor_ok.mp ‹_›, ‹_›, rfl, rfl, rfl⟩

/-- The pending deposits of an epoch keep one balance for each validator. -/
theorem balancesMatch_processPendingDeposits {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after)
    (holds : BalancesMatch state) : BalancesMatch after := by
  obtain ⟨_, _, _, _, pass, _, _, _, _, passed, validators, balances, _⟩ :=
    processPendingDeposits_pass computed
  have kept := balancesMatch_passPendingDeposits passed holds
  unfold BalancesMatch at kept ⊢
  rw [validators, balances]
  exact kept

/-- The pending deposits of an epoch leave a queue at most as long as before. -/
theorem processPendingDeposits_size_le {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    (after.pendingDeposits electra).data.size ≤ (state.pendingDeposits electra).data.size := by
  obtain ⟨_, _, _, _, pass, _, _, _, _, passed, _, _, queue⟩ := processPendingDeposits_pass computed
  have fits := pass.2
  simp only [Array.size_empty, Nat.add_zero, Array.length_toList] at fits
  rw [queue, Array.size_append, List.size_toArray]
  exact fits

/-- A pass reads a prefix of its deposits, at most what the limit per epoch still allows.

It applies some of those in order, and postpones the others in order.

It reads no deposit for which `stop` is true. -/
theorem passPendingDeposits_applied {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      ∃ read applied moved : List PendingDeposit,
        deposits = read ++ pass.1.rest ∧
          pass.1.postponed.toList = postponed.toList ++ moved ∧
          read.length ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat - count ∧
          applied.Sublist read ∧ moved.Sublist read ∧ (applied ++ moved).Perm read ∧
          applied.foldlM (applyPendingDeposit config checks) state = .ok pass.1.state ∧
          ∀ deposit ∈ read, stop deposit = false
  | [], _, _, _, _, _, computed => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨[], [], [], rfl, by simp, by simp, List.nil_sublist _, List.nil_sublist _,
      List.Perm.refl _, rfl, by simp⟩
  | deposit :: rest, state, processed, count, postponed, pass, computed => by
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      exact ⟨[], [], [], rfl, by simp, by simp, List.nil_sublist _, List.nil_sublist _,
        List.Perm.refl _, rfl, by simp⟩
    rename_i continues
    -- The pass reads this deposit, so `stop` is false there and the count is below the limit.
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true,
      Nat.not_le] at continues
    obtain ⟨reads, below⟩ := continues
    split at computed
    · split at computed
      · cases computed
      rename_i step
      split at computed
      · cases computed
      cases computed
      obtain ⟨read, applied, moved, queue, pushed, length, inRead, movedInRead, perm,
        later, noneStop⟩ := passPendingDeposits_applied (deposits := rest) ‹_›
      refine ⟨deposit :: read, deposit :: applied, moved, congrArg (deposit :: ·) queue, pushed,
        by simp only [List.length_cons]; omega, inRead.cons_cons _, movedInRead.cons _,
        perm.cons deposit, ?_, List.forall_mem_cons.mpr ⟨reads, noneStop⟩⟩
      simp only [List.foldlM_cons, bind, Except.bind, step]
      exact later
    split at computed
    · split at computed
      · cases computed
      cases computed
      obtain ⟨read, applied, moved, queue, pushed, length, inRead, movedInRead, perm,
        later, noneStop⟩ := passPendingDeposits_applied (deposits := rest) ‹_›
      refine ⟨deposit :: read, applied, deposit :: moved, congrArg (deposit :: ·) queue, ?_,
        by simp only [List.length_cons]; omega, inRead.cons _, movedInRead.cons_cons _,
        List.perm_middle.trans (perm.cons deposit), later,
        List.forall_mem_cons.mpr ⟨reads, noneStop⟩⟩
      -- The deposit waits after those that earlier steps postponed.
      rw [pushed, Array.toList_push, List.append_assoc]
      rfl
    split at computed
    · cases computed
    split at computed
    · cases computed
      exact ⟨[], [], [], rfl, by simp, by simp, List.nil_sublist _, List.nil_sublist _,
        List.Perm.refl _, rfl, by simp⟩
    split at computed
    · cases computed
    rename_i step
    split at computed
    · cases computed
    cases computed
    obtain ⟨read, applied, moved, queue, pushed, length, inRead, movedInRead, perm,
      later, noneStop⟩ := passPendingDeposits_applied (deposits := rest) ‹_›
    refine ⟨deposit :: read, deposit :: applied, moved, congrArg (deposit :: ·) queue, pushed,
      by simp only [List.length_cons]; omega, inRead.cons_cons _, movedInRead.cons _,
      perm.cons deposit, ?_, List.forall_mem_cons.mpr ⟨reads, noneStop⟩⟩
    simp only [List.foldlM_cons, bind, Except.bind, step]
    exact later

/-- The pending deposits of an epoch read a prefix of the queue, at most the limit per epoch.

They apply some of those in order, and move the others to the end of the queue in order.

The state after is the state of those applied, with a new queue and a new churn left over. -/
theorem processPendingDeposits_applied {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    ∃ (read rest applied postponed : List PendingDeposit) (next : BeaconState preset fork)
        (pending : PendingDeposits preset fork) (carried : Gwei),
      (state.pendingDeposits electra).data.toList = read ++ rest ∧
        pending.data.toList = rest ++ postponed ∧
        read.length ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat ∧
        applied.Sublist read ∧ postponed.Sublist read ∧ (applied ++ postponed).Perm read ∧
        applied.foldlM (applyPendingDeposit config checks) state = .ok next ∧
        after = { next with
          pendingDeposits := fun _ => pending
          depositBalanceToConsume := fun _ => carried } := by
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  -- Each success ends in the same record, after a pass from count zero with nothing postponed.
  repeat' (split at computed <;> try cases computed)
  all_goals
    obtain ⟨read, applied, postponed, queue, pushed, length, inRead, postponedInRead, perm,
      later, _⟩ := passPendingDeposits_applied ‹_›
    exact ⟨read, _, applied, postponed, _, _, _, queue, by simpa using pushed,
      by simpa using length, inRead, postponedInRead, perm, later, rfl⟩

/-- The queue before splits into the deposits added, the deposits dropped, and the queue after.

The sum of the balances rises by the amounts added.

Each dropped deposit is droppable at the state before.

That needs one balance for each validator.

It also needs room in 64 bits for the registry and the limit per epoch. -/
theorem processPendingDeposits_partition {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after)
    (holds : BalancesMatch state)
    (room : state.validators.data.size + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat < 2 ^ 64) :
    ∃ added dropped : List PendingDeposit,
      (added ++ dropped ++ (after.pendingDeposits electra).data.toList).Perm
          (state.pendingDeposits electra).data.toList ∧
        (∀ deposit ∈ dropped, DepositDroppable config checks state deposit) ∧
        balanceSum after = balanceSum state + pendingAmount added := by
  obtain ⟨read, rest, applied, postponed, next, pending, carried, queue, kept, length, inRead, _,
    perm, later, rfl⟩ := processPendingDeposits_applied computed
  have fits := inRead.length_le
  obtain ⟨added, dropped, split, all, sum⟩ :=
    foldlM_applyPendingDeposit_partition later holds (by omega)
  refine ⟨added, dropped, ?_, all, sum⟩
  change (added ++ dropped ++ pending.data.toList).Perm _
  rw [queue, kept]
  -- The queue before is `read ++ rest`, and `read` holds `applied` and `postponed` together.
  refine (split.append_right _).trans ((List.perm_append_comm.append_left applied).trans ?_)
  rw [← List.append_assoc]
  exact perm.append_right rest

/-- The pending deposits of an epoch never raise the balances plus the amounts in the queue. -/
theorem processPendingDeposits_total_le {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    balanceSum after + pendingAmount (after.pendingDeposits electra).data.toList ≤
      balanceSum state + pendingAmount (state.pendingDeposits electra).data.toList := by
  obtain ⟨read, rest, applied, postponed, next, pending, carried, queue, kept, _, _, _, perm,
    later, rfl⟩ := processPendingDeposits_applied computed
  have raised := foldlM_applyPendingDeposit_le later
  have amounts := (perm.map (·.amount.toNat)).sum_nat
  change balanceSum next + pendingAmount pending.data.toList ≤ _
  rw [queue, kept]
  simp only [pendingAmount, List.map_append, List.sum_append_nat] at amounts raised ⊢
  omega

/-- A deposit waits when its slot is after `finalizedSlot`.

It also waits when `bridgeDepositsPending` holds and its slot is after the genesis slot.

It waits in no other case. -/
theorem depositWaits_eq_false_iff {finalizedSlot : Slot} {deposit : PendingDeposit} :
    depositWaits state finalizedSlot deposit = false ↔
      deposit.slot ≤ finalizedSlot ∧
        (bridgeDepositsPending state = true → deposit.slot ≤ GENESIS_SLOT) := by
  simp only [depositWaits, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
    decide_eq_false_iff_not, UInt64.not_lt]
  cases bridgeDepositsPending state <;> simp [and_comm]

/-- A deposit leaves the queue of an epoch only if its slot is at most `finalizedSlot`.

That slot is the first slot of the finalized epoch.

In Electra, while deposits of the old mechanism remain, no request leaves it.

A deposit leaves when the queue after holds fewer copies of it than the queue before. -/
theorem processPendingDeposits_finalized {electra : .pectra ≤ fork} {finalizedSlot : Slot}
    {deposit : PendingDeposit}
    (computed : processPendingDeposits config checks state electra = .ok after)
    (start : computeStartSlotAtEpoch preset state.finalizedCheckpoint.epoch = .ok finalizedSlot)
    (fewer : (after.pendingDeposits electra).data.toList.count deposit <
      (state.pendingDeposits electra).data.toList.count deposit) :
    deposit.slot ≤ finalizedSlot ∧
      (bridgeDepositsPending state = true → deposit.slot ≤ GENESIS_SLOT) := by
  obtain ⟨_, _, _, waitSlot, pass, _, _, _, waitSlotOk, passed, _, _, queue⟩ :=
    processPendingDeposits_pass computed
  -- The pass waits for the first slot of the finalized epoch.
  obtain rfl : waitSlot = finalizedSlot :=
    Except.ok.inj ((mapError_ok_iff.mp waitSlotOk).symm.trans start)
  obtain ⟨read, _, moved, split, pushed, _, _, movedInRead, _, _, ready⟩ :=
    passPendingDeposits_applied passed
  -- The queue after holds the deposits not reached, then some of those read.
  have kept : (after.pendingDeposits electra).data.toList = pass.1.rest ++ moved := by
    rw [queue]
    simpa using pushed
  have before := congrArg (List.count deposit) split
  rw [kept] at fewer
  simp only [List.count_append] at fewer before
  have bound := movedInRead.count_le deposit
  exact depositWaits_eq_false_iff.mp (ready deposit (List.count_pos_iff.mp (by omega)))

end EthLib.Consensus
