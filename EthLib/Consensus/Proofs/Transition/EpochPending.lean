module

public import EthLib.Consensus.Proofs.Transition.Operations
public import EthLib.Consensus.Transition.EpochPending

/-!
# Proofs: the pending deposits of an epoch

The pending deposits of an epoch keep one balance for each validator.

The queue never grows.

A pass never credits more inside the churn than the churn available.

The churn that a pass uses grows by the amounts of the deposits it reads that take churn.

A pass reads a prefix of the queue, applies some of it in order, and postpones the others.

So the queue splits into the deposits added to the balances, those dropped, and the queue after.

A pass postpones exactly the deposits it reads whose validator exits and is not withdrawn.

The validators it tests are those at the start of the pass.

The balances plus the amounts in the queue never rise.

A pass that leaves deposits unread stops at its stop condition, the limit per epoch or the churn.

Only a pass that stops at the churn records that it reached the churn.

If it does, the churn that the pass did not use carries over to the next epoch, and else none does.

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
    · cases computed
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
    · cases computed
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

/-- A deposit keeps, at each epoch and key, the two tests of the validator with that key.

They ask whether it exits and whether it is withdrawn.

A new validator neither exits nor is withdrawn, as for a key that no validator has. -/
theorem depositTargetStatus_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    depositTargetStatus after = depositTargetStatus state := by
  funext nextEpoch pubkey
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      rfl
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · have pushed := addValidatorToRegistry_validators_eq_push computed
      -- The new validator has no exit before the far future, and no epoch passes the far future.
      have far : ¬FAR_FUTURE_EPOCH < nextEpoch := by
        rw [UInt64.lt_iff_toNat_lt]
        have := nextEpoch.toNat_lt
        have : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
        omega
      have small := addValidatorToRegistry_size_lt computed
      simp only [depositTargetStatus, pushed, Array.findIdx?_push]
      cases found : state.validators.data.findIdx? (·.pubkey == pubkey) with
      | some position =>
        -- The validator found before keeps its position, below the new one.
        obtain ⟨below, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp found
        simp only [Option.some_or, bind, Except.bind]
        cases converted : liftArith (ofNatChecked position) with
        | error _ => rfl
        | ok index =>
          simp only [getElem?_toNat_eq_of_ofNatChecked (mapError_ok_iff.mp converted),
            Array.getElem?_push_lt below, Array.getElem?_eq_getElem below]
      | none =>
        simp only [Option.none_or]
        by_cases key : deposit.pubkey = pubkey
        · simp [getValidatorFromDeposit, key, far, ofNatChecked_of_lt small, liftArith,
            Except.mapError, bind, Except.bind, pure, Except.pure, Nat.mod_eq_of_lt small]
        · simp [getValidatorFromDeposit, key]
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      rfl
  · simp only [liftAccessor_ok, bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    simp only [depositTargetStatus, increaseBalance_validators computed]

/-- The status of a deposit target never fails on an index.

The validator found with the key is the one that the read at its converted index finds. -/
theorem depositTargetStatus_ne_indexOutOfRange (state : BeaconState preset fork)
    (nextEpoch : Epoch) (pubkey : Cryptography.Bls.BLSPubkey) (index : ValidatorIndex) :
    depositTargetStatus state nextEpoch pubkey ≠ .error (.indexOutOfRange index) := by
  unfold depositTargetStatus
  split
  · rename_i position found
    obtain ⟨inside, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp found
    cases converted : ofNatChecked position with
    | error _ => simp [liftArith, Except.mapError, bind, Except.bind]
    | ok checked =>
      simp [liftArith, Except.mapError, bind, Except.bind,
        getElem?_toNat_eq_of_ofNatChecked converted, Array.getElem?_eq_getElem inside, pure,
        Except.pure]
  · simp [pure, Except.pure]

/-- The pending deposits of an epoch end with a pass over the queue from its front.

The pass reads the next epoch and the churn available.

That churn is the churn left from the last epoch and the churn of deposits.

It stops at a deposit that waits for the first slot of the finalized epoch.

The registry and the balances are those of the pass.

The queue holds the deposits that the pass did not reach, then those it postponed.

If the pass records that it reached the churn, the churn it did not use carries over.

Otherwise none carries over to the next epoch. -/
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
        (after.pendingDeposits electra).data = pass.1.rest.toArray ++ pass.1.postponed ∧
        (after.depositBalanceToConsume electra).toNat =
          if pass.1.churnReached then available.toNat - pass.1.processed.toNat else 0 := by
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals refine ⟨_, _, _, _, _, liftAccessor_ok.mp ‹_›, liftAccessor_ok.mp ‹_›,
    liftAccessor_ok.mp ‹_›, liftAccessor_ok.mp ‹_›, ‹_›, rfl, rfl, rfl, ?_⟩
  -- With the churn reached, the step subtracts the churn used, and else it carries none.
  · rename_i reached _ _ subtracted
    rw [ite_eq_left_of_eq_true _ _ (eq_true reached)]
    exact (subChecked_ok_iff.mp (mapError_ok_iff.mp (liftAccessor_ok.mp subtracted))).2
  · rename_i unreached
    rw [ite_eq_right_of_eq_false _ _ (eq_false unreached)]
    rfl

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
  obtain ⟨_, _, _, _, pass, _, _, _, _, passed, _, _, queue, _⟩ :=
    processPendingDeposits_pass computed
  have fits := pass.2
  simp only [Array.size_empty, Nat.add_zero, Array.length_toList] at fits
  rw [queue, Array.size_append, List.size_toArray]
  exact fits

/-- A found pair of tests is two false tests exactly when neither test holds. -/
private theorem some_beq_false_false {status : Bool × Bool} :
    (some status == some (false, false)) = (!status.1 && !status.2) := by
  cases status with
  | mk exited withdrawn => cases exited <;> cases withdrawn <;> rfl

/-- A found pair of tests is a true test then a false test exactly when only the first holds. -/
private theorem some_beq_true_false {status : Bool × Bool} :
    (some status == some (true, false)) = (status.1 && !status.2) := by
  cases status with
  | mk exited withdrawn => cases exited <;> cases withdrawn <;> rfl

/-- What a pass does with `read`, the deposits that it reads.

They are a prefix of its deposits, at most what the limit per epoch still allows.

It applies `applied` in order, and postpones `moved` in order, and the two make up `read`.

It reads no deposit for which `stop` is true.

If deposits remain, it stopped at one for which `stop` is true, or at the limit per epoch.

Otherwise that deposit takes churn, and it would take more than the churn available.

After the deposits it applied, no validator with its key exits or is withdrawn.

The pass records that it reached the churn.

In every other case it records that it did not reach the churn.

The churn that it uses grows by the amount of each deposit it reads that takes churn.

Those are the deposits whose validator, at the start of the pass, neither exits nor is withdrawn.

The churn grows by nothing else.

`moved` holds exactly the deposits of `read` whose validator exits and is not withdrawn.

As for the churn, the validators are those at the start of the pass.

`applied` holds the others.

The tests of a deposit that the pass reads succeed, so the filters may read them as options. -/
structure PassPendingDepositsFacts (config : Config) (checks : SignatureChecks)
    (stop : PendingDeposit → Bool) (nextEpoch : Epoch) (available : Gwei)
    (state : BeaconState preset fork) (processed : Gwei) (count : Nat)
    (postponed : Array PendingDeposit) (deposits : List PendingDeposit)
    (pass : PendingDepositsPass preset fork) (read applied moved : List PendingDeposit) : Prop where
  split : deposits = read ++ pass.rest
  pushed : pass.postponed.toList = postponed.toList ++ moved
  bounded : read.length ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat - count
  appliedSublist : applied.Sublist read
  movedSublist : moved.Sublist read
  perm : (applied ++ moved).Perm read
  applies : applied.foldlM (applyPendingDeposit config checks) state = .ok pass.state
  noneStop : ∀ deposit ∈ read, stop deposit = false
  stops : ∀ deposit tail, pass.rest = deposit :: tail →
    stop deposit = true ∨ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat ≤ count + read.length ∨
      (depositTargetStatus pass.state nextEpoch deposit.pubkey = .ok (false, false) ∧
        available.toNat < pass.processed.toNat + deposit.amount.toNat ∧ pass.churnReached = true)
  reached : pass.churnReached = true →
    ∃ deposit tail, pass.rest = deposit :: tail ∧ stop deposit = false ∧
      count + read.length < preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat
  used : pass.processed.toNat = processed.toNat + pendingAmount (read.filter fun deposit =>
      (depositTargetStatus state nextEpoch deposit.pubkey).toOption == some (false, false))
  appliedFilter : applied = read.filter fun deposit =>
      (depositTargetStatus state nextEpoch deposit.pubkey).toOption != some (true, false)
  movedFilter : moved = read.filter fun deposit =>
      (depositTargetStatus state nextEpoch deposit.pubkey).toOption == some (true, false)
  statusOk : ∀ deposit ∈ read, ∃ status,
    depositTargetStatus state nextEpoch deposit.pubkey = .ok status

/-- A pass reads a prefix of its deposits, applies some of them and postpones the others.

It also counts its churn.

It postpones exactly those it reads whose validator exits and is not withdrawn. -/
theorem passPendingDeposits_applied {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      ∃ read applied moved : List PendingDeposit,
        PassPendingDepositsFacts config checks stop nextEpoch available state processed count
          postponed deposits pass.1 read applied moved
  | [], _, _, _, _, _, computed => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨[], [], [], rfl, by simp, by simp, List.nil_sublist _, List.nil_sublist _,
      List.Perm.refl _, rfl, by simp, by simp, by simp, by simp [pendingAmount],
      rfl, rfl, by simp⟩
  | deposit :: rest, state, processed, count, postponed, pass, computed => by
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · rename_i stopped
      cases computed
      refine ⟨[], [], [], rfl, by simp, by simp, List.nil_sublist _, List.nil_sublist _,
        List.Perm.refl _, rfl, by simp, ?_, by simp, by simp [pendingAmount],
        rfl, rfl, by simp⟩
      rintro _ _ ⟨⟩
      simp only [Bool.or_eq_true, decide_eq_true_eq] at stopped
      exact stopped.imp_right Or.inl
    rename_i continues
    -- The pass reads this deposit, so `stop` is false there and the count is below the limit.
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true,
      Nat.not_le] at continues
    obtain ⟨reads, below⟩ := continues
    split at computed
    · cases computed
    rename_i status found
    -- The pass reads the two tests of the validator with the key of the deposit.
    have known : (depositTargetStatus state nextEpoch deposit.pubkey).toOption = some status := by
      simp [liftAccessor_ok.mp found, Except.toOption]
    split at computed
    · rename_i isWithdrawn
      split at computed
      · cases computed
      rename_i step
      split at computed
      · cases computed
      cases computed
      obtain ⟨read, applied, moved, facts⟩ := passPendingDeposits_applied (deposits := rest) ‹_›
      have within := facts.bounded
      -- A deposit credited outside the churn does not wait.
      have notMoved :
          (some status == some (true, false)) = false := by
        rw [some_beq_true_false]; simp [isWithdrawn]
      refine ⟨deposit :: read, deposit :: applied, moved,
        { split := congrArg (deposit :: ·) facts.split
          pushed := facts.pushed
          bounded := by simp only [List.length_cons]; omega
          appliedSublist := facts.appliedSublist.cons_cons _
          movedSublist := facts.movedSublist.cons _
          perm := facts.perm.cons deposit
          applies := ?_
          noneStop := List.forall_mem_cons.mpr ⟨reads, facts.noneStop⟩
          stops := fun _ _ head => (facts.stops _ _ head).imp_right
            (Or.imp_left (by simp only [List.length_cons]; omega))
          reached := fun flagged => (facts.reached flagged).imp fun _ =>
            .imp fun _ ⟨front, unstopped, under⟩ =>
              ⟨front, unstopped, by simp only [List.length_cons]; omega⟩
          used := ?_
          appliedFilter := ?_
          movedFilter := ?_
          statusOk := List.forall_mem_cons.mpr ⟨⟨status, liftAccessor_ok.mp found⟩, by
            rw [← depositTargetStatus_applyPendingDeposit step]
            exact facts.statusOk⟩ }⟩
      · simp only [List.foldlM_cons, bind, Except.bind, step]
        exact facts.applies
      all_goals
        -- The rest of the pass tests the state after the deposit, which keeps both tests per key.
        have kept := depositTargetStatus_applyPendingDeposit step
      · have used := facts.used
        rw [kept] at used
        -- A deposit credited outside the churn takes none of it.
        have outside :
            (some status == some (false, false)) = false := by
          rw [some_beq_false_false]; simp [isWithdrawn]
        simp only [List.filter_cons, known, outside, Bool.false_eq_true, ↓reduceIte, used]
      · have filtered := facts.appliedFilter
        rw [kept] at filtered
        simp only [List.filter_cons, known, bne, notMoved, Bool.not_false, ↓reduceIte, filtered]
      · have filtered := facts.movedFilter
        rw [kept] at filtered
        simp only [List.filter_cons, known, notMoved, Bool.false_eq_true, ↓reduceIte, filtered]
    rename_i notWithdrawn
    split at computed
    · rename_i isExited
      split at computed
      · cases computed
      cases computed
      obtain ⟨read, applied, moved, facts⟩ := passPendingDeposits_applied (deposits := rest) ‹_›
      have within := facts.bounded
      -- Its validator exits and is not withdrawn, so the deposit waits.
      have isMoved :
          (some status == some (true, false)) = true := by
        simp only [Bool.not_eq_true] at notWithdrawn
        rw [some_beq_true_false]; simp [isExited, notWithdrawn]
      refine ⟨deposit :: read, applied, deposit :: moved,
        { split := congrArg (deposit :: ·) facts.split
          pushed := ?_
          bounded := by simp only [List.length_cons]; omega
          appliedSublist := facts.appliedSublist.cons _
          movedSublist := facts.movedSublist.cons_cons _
          perm := List.perm_middle.trans (facts.perm.cons deposit)
          applies := facts.applies
          noneStop := List.forall_mem_cons.mpr ⟨reads, facts.noneStop⟩
          stops := fun _ _ head => (facts.stops _ _ head).imp_right
            (Or.imp_left (by simp only [List.length_cons]; omega))
          reached := fun flagged => (facts.reached flagged).imp fun _ =>
            .imp fun _ ⟨front, unstopped, under⟩ =>
              ⟨front, unstopped, by simp only [List.length_cons]; omega⟩
          used := ?_
          appliedFilter := ?_
          movedFilter := ?_
          statusOk := List.forall_mem_cons.mpr
            ⟨⟨status, liftAccessor_ok.mp found⟩, facts.statusOk⟩ }⟩
      · -- The deposit waits after those that earlier steps postponed.
        rw [facts.pushed, Array.toList_push, List.append_assoc]
        rfl
      · have used := facts.used
        -- A deposit postponed takes no churn.
        have outside :
            (some status == some (false, false)) = false := by
          rw [some_beq_false_false]; simp [isExited]
        simp only [List.filter_cons, known, outside, Bool.false_eq_true, ↓reduceIte, used]
      · have filtered := facts.appliedFilter
        simp only [List.filter_cons, known, bne, isMoved, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, filtered]
      · have filtered := facts.movedFilter
        simp only [List.filter_cons, known, isMoved, ↓reduceIte, filtered]
    rename_i notExited
    simp only [Bool.not_eq_true] at notWithdrawn notExited
    split at computed
    · cases computed
    rename_i total checked
    have sum := (addChecked_ok_iff.mp (mapError_ok_iff.mp (liftAccessor_ok.mp checked))).2
    -- The deposit takes churn, since neither test of its validator held.
    have inside :
        (some status == some (false, false)) = true := by
      rw [some_beq_false_false]; simp [notExited, notWithdrawn]
    split at computed
    · rename_i over
      cases computed
      -- The deposit does not fit in the churn available.
      have beyond : available.toNat < processed.toNat + deposit.amount.toNat := by
        have := UInt64.lt_iff_toNat_lt.mp over
        omega
      refine ⟨[], [], [], rfl, by simp, by simp, List.nil_sublist _, List.nil_sublist _,
        List.Perm.refl _, rfl, by simp, ?_,
        fun _ => ⟨deposit, rest, rfl, reads, by simpa using below⟩,
        by simp [pendingAmount], rfl, rfl, by simp⟩
      rintro _ _ ⟨⟩
      exact Or.inr (Or.inr ⟨(liftAccessor_ok.mp found).trans
        (congrArg _ (Prod.ext notExited notWithdrawn)), beyond, rfl⟩)
    split at computed
    · cases computed
    rename_i step
    split at computed
    · cases computed
    cases computed
    obtain ⟨read, applied, moved, facts⟩ := passPendingDeposits_applied (deposits := rest) ‹_›
    have within := facts.bounded
    -- The deposit takes churn, so it does not wait.
    have notMoved :
        (some status == some (true, false)) = false := by
      rw [some_beq_true_false]; simp [notExited]
    refine ⟨deposit :: read, deposit :: applied, moved,
      { split := congrArg (deposit :: ·) facts.split
        pushed := facts.pushed
        bounded := by simp only [List.length_cons]; omega
        appliedSublist := facts.appliedSublist.cons_cons _
        movedSublist := facts.movedSublist.cons _
        perm := facts.perm.cons deposit
        applies := ?_
        noneStop := List.forall_mem_cons.mpr ⟨reads, facts.noneStop⟩
        stops := fun _ _ head => (facts.stops _ _ head).imp_right
          (Or.imp_left (by simp only [List.length_cons]; omega))
        reached := fun flagged => (facts.reached flagged).imp fun _ =>
          .imp fun _ ⟨front, unstopped, under⟩ =>
            ⟨front, unstopped, by simp only [List.length_cons]; omega⟩
        used := ?_
        appliedFilter := ?_
        movedFilter := ?_
        statusOk := List.forall_mem_cons.mpr ⟨⟨status, liftAccessor_ok.mp found⟩, by
          rw [← depositTargetStatus_applyPendingDeposit step]
          exact facts.statusOk⟩ }⟩
    · simp only [List.foldlM_cons, bind, Except.bind, step]
      exact facts.applies
    all_goals
      -- The rest of the pass tests the state after the deposit, which keeps both tests at each key.
      have kept := depositTargetStatus_applyPendingDeposit step
    · have used := facts.used
      rw [kept] at used
      simp only [List.filter_cons, known, inside, ↓reduceIte, pendingAmount, List.map_cons,
        List.sum_cons] at used ⊢
      omega
    · have filtered := facts.appliedFilter
      rw [kept] at filtered
      simp only [List.filter_cons, known, bne, notMoved, Bool.not_false, ↓reduceIte, filtered]
    · have filtered := facts.movedFilter
      rw [kept] at filtered
      simp only [List.filter_cons, known, notMoved, Bool.false_eq_true, ↓reduceIte, filtered]

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
    obtain ⟨read, applied, postponed, facts⟩ := passPendingDeposits_applied ‹_›
    exact ⟨read, _, applied, postponed, _, _, _, facts.split, by simpa using facts.pushed,
      by simpa using facts.bounded, facts.appliedSublist, facts.movedSublist, facts.perm,
      facts.applies, rfl⟩

/-- The pending deposits of an epoch read a prefix of the queue, at most the limit per epoch.

They postpone those whose validator, in the state before, exits and is not withdrawn.

Withdrawn means withdrawable before the next epoch.

They apply the others in order, and move the postponed ones to the end of the queue in order.

The state after is the state of those applied, with a new queue and a new churn left over.

The two tests of each deposit read succeed. -/
theorem processPendingDeposits_postponed {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    ∃ (read rest : List PendingDeposit) (next : BeaconState preset fork)
        (pending : PendingDeposits preset fork) (carried : Gwei),
      (state.pendingDeposits electra).data.toList = read ++ rest ∧
        pending.data.toList = rest ++ read.filter (fun deposit =>
          (depositTargetStatus state (getCurrentEpoch state + 1) deposit.pubkey).toOption ==
            some (true, false)) ∧
        read.length ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat ∧
        (∀ deposit ∈ read, ∃ status,
          depositTargetStatus state (getCurrentEpoch state + 1) deposit.pubkey = .ok status) ∧
        (read.filter fun deposit =>
            (depositTargetStatus state (getCurrentEpoch state + 1) deposit.pubkey).toOption !=
              some (true, false)).foldlM (applyPendingDeposit config checks) state = .ok next ∧
        after = { next with
          pendingDeposits := fun _ => pending
          depositBalanceToConsume := fun _ => carried } := by
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  -- Each success ends in the same record, after a pass from count zero with nothing postponed.
  repeat' (split at computed <;> try cases computed)
  all_goals
    -- The next epoch that the step computes is the wrapping sum, since the step succeeds.
    have added := liftAccessor_ok.mp
      ‹liftAccessor (liftArith (addChecked (getCurrentEpoch state) 1)) = .ok _›
    rw [liftArith, mapError_ok_iff, addChecked_ok_iff] at added
    obtain rfl := UInt64.toNat_inj.mp (added.2.trans (toNat_add_of_lt added.1).symm)
    obtain ⟨read, applied, _, facts⟩ := passPendingDeposits_applied ‹_›
    have applies := facts.applies
    rw [facts.appliedFilter] at applies
    refine ⟨read, _, _, _, _, facts.split, ?_, by simpa using facts.bounded, facts.statusOk,
      applies, rfl⟩
    rw [← facts.movedFilter]
    simpa using facts.pushed

/-- The queue before splits into the deposits added, the deposits dropped, and the queue after.

The sum of the balances rises by the amounts added.

Each dropped deposit is droppable at the state before.

That needs one balance for each validator. -/
theorem processPendingDeposits_partition {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after)
    (holds : BalancesMatch state) :
    ∃ added dropped : List PendingDeposit,
      (added ++ dropped ++ (after.pendingDeposits electra).data.toList).Perm
          (state.pendingDeposits electra).data.toList ∧
        (∀ deposit ∈ dropped, DepositDroppable config checks state deposit) ∧
        balanceSum after = balanceSum state + pendingAmount added := by
  obtain ⟨read, rest, applied, postponed, next, pending, carried, queue, kept, length, inRead, _,
    perm, later, rfl⟩ := processPendingDeposits_applied computed
  obtain ⟨added, dropped, split, all, sum⟩ :=
    foldlM_applyPendingDeposit_partition later holds
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
  obtain ⟨_, _, _, waitSlot, pass, _, _, _, waitSlotOk, passed, _, _, queue, _⟩ :=
    processPendingDeposits_pass computed
  -- The pass waits for the first slot of the finalized epoch.
  obtain rfl : waitSlot = finalizedSlot :=
    Except.ok.inj ((mapError_ok_iff.mp waitSlotOk).symm.trans start)
  obtain ⟨read, _, moved, facts⟩ := passPendingDeposits_applied passed
  -- The queue after holds the deposits not reached, then some of those read.
  have kept : (after.pendingDeposits electra).data.toList = pass.1.rest ++ moved := by
    rw [queue]
    simpa using facts.pushed
  have before := congrArg (List.count deposit) facts.split
  rw [kept] at fewer
  simp only [List.count_append] at fewer before
  have bound := facts.movedSublist.count_le deposit
  exact depositWaits_eq_false_iff.mp (facts.noneStop deposit (List.count_pos_iff.mp (by omega)))

end EthLib.Consensus
