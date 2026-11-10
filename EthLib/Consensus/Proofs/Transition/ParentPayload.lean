module

public import EthLib.Consensus.Proofs.Builders
public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Consensus.Transition.ParentPayload

/-!
# Proofs: the parent payload

An empty parent leaves the state as it is when the block carries no request.

It rejects a block that carries a request.

A parent payload step succeeds only when four lists of requests fit their limits.

A step that succeeds finds the parent empty, or settles and runs the requests of a full parent.

A full parent records its block hash, and marks its slot as having a payload.

The payment of its builder changes only the queues of builder payments and withdrawals.

It empties at most one pending payment, and keeps the builders.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork} {gloas : .glamsterdam ≤ fork}

/-- An empty parent leaves the state as it is when the block carries no request. -/
theorem processParentExecutionPayload_of_empty {body : BeaconBlockBody preset fork}
    (empty : (body.signedExecutionPayloadBid gloas).message.parentBlockHash ≠
      (state.latestExecutionPayloadBid gloas).blockHash)
    (noRequest : (body.parentExecutionRequests gloas).isEmpty gloas = true) :
    processParentExecutionPayload config checks state gloas body = .ok state := by
  simp [processParentExecutionPayload, empty, noRequest, ensure, bind, Except.bind, pure,
    Except.pure]

/-- An empty parent rejects a block that carries a request. -/
theorem processParentExecutionPayload_of_empty_requests {body : BeaconBlockBody preset fork}
    (empty : (body.signedExecutionPayloadBid gloas).message.parentBlockHash ≠
      (state.latestExecutionPayloadBid gloas).blockHash)
    (requests : (body.parentExecutionRequests gloas).isEmpty gloas = false) :
    processParentExecutionPayload config checks state gloas body =
      .error .parentRequestsNotEmpty := by
  simp [processParentExecutionPayload, empty, requests, ensure, bind, Except.bind]

/-- A parent payload step succeeds only when four lists of requests fit their limits.

An empty parent takes no request, and a full parent checks the four counts. -/
theorem processParentExecutionPayload_counts {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    (body.parentExecutionRequests gloas).withdrawals.data.size ≤
        preset.MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD.toNat ∧
      (body.parentExecutionRequests gloas).consolidations.data.size ≤
        preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat ∧
      ((body.parentExecutionRequests gloas).builderDeposits gloas).data.size ≤
        preset.MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD.toNat ∧
      ((body.parentExecutionRequests gloas).builderExits gloas).data.size ≤
        preset.MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD.toNat := by
  unfold processParentExecutionPayload at computed
  dsimp only at computed
  -- A bid that does not build on the parent bid finds the parent empty.
  split at computed
  · obtain ⟨_, empty, -⟩ := bind_ok_iff.mp computed
    rw [ensure_ok_iff] at empty
    simp only [ExecutionRequests.isEmpty, Bool.and_eq_true, Array.isEmpty_iff] at empty
    obtain ⟨⟨⟨⟨-, withdrawals⟩, consolidations⟩, builderDeposits⟩, exits⟩ := empty
    simp [withdrawals, consolidations, builderDeposits, exits]
  -- A full parent checks the root of its requests, then their four counts.
  · simp only [bind_ok_iff, ensure_ok_iff, applyParentExecutionPayload, checkCount] at computed
    obtain ⟨_, -, _, -, _, withdrawals, _, consolidations, _, builderDeposits, _, exits, -⟩ :=
      computed
    exact ⟨withdrawals, consolidations, builderDeposits, exits⟩

/-- A full parent settles the payment of its builder, then runs each list of its requests in order.

The deposits run first, then the withdrawals, the consolidations, and the requests of builders.

It then marks the slot of the parent as having a payload.

The hash of the parent bid becomes the latest block hash.

The checks of the counts of the requests come before, and are left out here. -/
theorem applyParentExecutionPayload_ok {requests : ExecutionRequests preset fork}
    (computed : applyParentExecutionPayload config checks state gloas requests = .ok after) :
    ∃ settled deposited withdrawn consolidated builderDeposited exited bits,
      settleParentPayment state gloas = .ok settled ∧
      requests.deposits.data.toList.foldlM
        (processDepositRequest · (Nat.le_trans (by decide) gloas) ·) settled = .ok deposited ∧
      requests.withdrawals.data.toList.foldlM
        (processWithdrawalRequest config · (Nat.le_trans (by decide) gloas) ·) deposited =
        .ok withdrawn ∧
      requests.consolidations.data.toList.foldlM
        (processConsolidationRequest config · (Nat.le_trans (by decide) gloas) ·) withdrawn =
        .ok consolidated ∧
      (requests.builderDeposits gloas).data.toList.foldlM
        (processBuilderDepositRequest config checks · gloas ·) consolidated =
        .ok builderDeposited ∧
      (requests.builderExits gloas).data.toList.foldlM
        (processBuilderExitRequest config · gloas ·) builderDeposited = .ok exited ∧
      writeCircular (exited.executionPayloadAvailability gloas).bits
        state.latestBlockHeader.slot true = .ok bits ∧
      after = { exited with
        executionPayloadAvailability := fun _ => ⟨bits⟩
        latestBlockHash := fun _ => (state.latestExecutionPayloadBid gloas).blockHash } := by
  simp only [bind_ok_iff, applyParentExecutionPayload, processParentRequests, pure, Except.pure,
    Except.ok.injEq, ← Array.foldlM_toList] at computed
  obtain ⟨_, -, _, -, _, -, _, -, settled, settledOk, _, ⟨deposited, depositsOk,
    withdrawn, withdrawalsOk, consolidated, consolidationsOk, builderDeposited, buildersOk,
    exitsOk⟩, bits, written, rfl⟩ := computed
  exact ⟨settled, deposited, withdrawn, consolidated, builderDeposited, _, bits, settledOk,
    depositsOk, withdrawalsOk, consolidationsOk, buildersOk, exitsOk, liftAccessor_ok.mp written,
    rfl⟩

/-- A parent payload step that succeeds finds the parent empty or full.

An empty parent takes no request and leaves the state as it is.

A full parent settles the payment of its builder, then runs each list of its requests in order.

The deposits run first, then the withdrawals, the consolidations, and the requests of builders.

It then marks the slot of the parent as having a payload.

The hash of the parent bid becomes the latest block hash.

The checks of the root and the counts of the requests come before, and are left out here. -/
theorem processParentExecutionPayload_ok {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    ((body.signedExecutionPayloadBid gloas).message.parentBlockHash ≠
        (state.latestExecutionPayloadBid gloas).blockHash ∧
      (body.parentExecutionRequests gloas).isEmpty gloas = true ∧ after = state) ∨
    ((body.signedExecutionPayloadBid gloas).message.parentBlockHash =
        (state.latestExecutionPayloadBid gloas).blockHash ∧
      ∃ settled deposited withdrawn consolidated builderDeposited exited bits,
        settleParentPayment state gloas = .ok settled ∧
        (body.parentExecutionRequests gloas).deposits.data.toList.foldlM
          (processDepositRequest · (Nat.le_trans (by decide) gloas) ·) settled = .ok deposited ∧
        (body.parentExecutionRequests gloas).withdrawals.data.toList.foldlM
          (processWithdrawalRequest config · (Nat.le_trans (by decide) gloas) ·) deposited =
          .ok withdrawn ∧
        (body.parentExecutionRequests gloas).consolidations.data.toList.foldlM
          (processConsolidationRequest config · (Nat.le_trans (by decide) gloas) ·) withdrawn =
          .ok consolidated ∧
        ((body.parentExecutionRequests gloas).builderDeposits gloas).data.toList.foldlM
          (processBuilderDepositRequest config checks · gloas ·) consolidated =
          .ok builderDeposited ∧
        ((body.parentExecutionRequests gloas).builderExits gloas).data.toList.foldlM
          (processBuilderExitRequest config · gloas ·) builderDeposited = .ok exited ∧
        writeCircular (exited.executionPayloadAvailability gloas).bits
          state.latestBlockHeader.slot true = .ok bits ∧
        after = { exited with
          executionPayloadAvailability := fun _ => ⟨bits⟩
          latestBlockHash := fun _ => (state.latestExecutionPayloadBid gloas).blockHash }) := by
  unfold processParentExecutionPayload at computed
  dsimp only at computed
  split at computed
  · rename_i empty
    obtain ⟨_, noRequest, done⟩ := bind_ok_iff.mp computed
    simp only [pure, Except.pure, Except.ok.injEq] at done
    exact .inl ⟨empty, ensure_ok_iff.mp noRequest, done.symm⟩
  rename_i full
  simp only [bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, -, -, -, applied⟩ := computed
  exact .inr ⟨Decidable.of_not_not full, applyParentExecutionPayload_ok applied⟩

/-- A full parent makes the hash of its bid the latest block hash. -/
theorem applyParentExecutionPayload_latestBlockHash {requests : ExecutionRequests preset fork}
    (computed : applyParentExecutionPayload config checks state gloas requests = .ok after) :
    after.latestBlockHash gloas = (state.latestExecutionPayloadBid gloas).blockHash := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ :=
    applyParentExecutionPayload_ok computed
  rfl

/-- A full parent marks its slot as having a payload.

The bit of its slot, modulo the length of the record, is set. -/
theorem applyParentExecutionPayload_available {requests : ExecutionRequests preset fork}
    (computed : applyParentExecutionPayload config checks state gloas requests = .ok after) :
    (after.executionPayloadAvailability gloas).bits[
      (state.latestBlockHeader.slot % preset.SLOTS_PER_HISTORICAL_ROOT).toNat]? = some true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, written, rfl⟩ :=
    applyParentExecutionPayload_ok computed
  exact getElem?_writeCircular written

/-- The payment of the parent's builder changes only the queues of builder payments and withdrawals.
-/
theorem settleParentPayment_eq (computed : settleParentPayment state gloas = .ok after) :
    after = { state with
      builderPendingWithdrawals := after.builderPendingWithdrawals
      builderPendingPayments := after.builderPendingPayments } := by
  unfold settleParentPayment at computed
  split at computed
  · have set := liftAccessor_ok.mp computed
    unfold settleBuilderPayment at set
    split at set
    · cases set
      rfl
    · cases set
  · dsimp only at computed
    split at computed <;> cases computed <;> rfl

/-- The payment of the parent's builder changes no pending payment but the one it settles.

That one is at the position of the parent's slot, when the parent is of this epoch or the last. -/
theorem settleParentPayment_payments
    (computed : settleParentPayment state gloas = .ok after) (index : Nat)
    (inRange : index < 2 * preset.SLOTS_PER_EPOCH.toNat)
    (other : (parentPaymentPosition state).map UInt64.toNat ≠ some index) :
    (after.builderPendingPayments gloas)[index] = (state.builderPendingPayments gloas)[index] := by
  unfold settleParentPayment at computed
  split at computed
  · rename_i position settled
    obtain ⟨_, payments, _⟩ := settleBuilderPayment_spec (liftAccessor_ok.mp computed)
    rw [settled] at other
    simp only [Option.map_some, ne_eq, Option.some.injEq] at other
    simp only [payments]
    exact Serialization.Ssz.RootedVector.getElem_set_ne _ _ _ _ other
  · dsimp only at computed
    split at computed <;> cases computed <;> rfl

/-- The payment of the parent's builder keeps the registry of builders. -/
theorem settleParentPayment_builders (computed : settleParentPayment state gloas = .ok after) :
    after.builders = state.builders := by
  rw [settleParentPayment_eq computed]

end EthLib.Consensus
