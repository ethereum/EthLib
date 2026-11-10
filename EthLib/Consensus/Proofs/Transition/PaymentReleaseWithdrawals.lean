module

public import EthLib.Consensus.Proofs.Transition.PayloadInputs
public import EthLib.Consensus.Proofs.Transition.PaymentRelease
public import EthLib.Consensus.Proofs.Transition.Withdrawals

/-!
# Proofs: the withdrawals of a block and the bids it pays

From Gloas the builder of a block pays its proposer through a pending payment.

Inside a block, the withdrawals take a prefix of the queue of builder withdrawals.

So the steps of a block are named by a relation where the queue may lose a prefix.

It loses it after it gains the released withdrawals.

Each payment that such a step releases is closed after it.

A step that releases payments, then a step that releases none, release those payments together.

The withdrawals of a block release no payment.

[EIP-7732] adds the builders, their bids, their payments and their withdrawals.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-- A step that queues the withdrawals of open payments, then may drop a prefix of the queue.

No slot is twice in the list, and each slot of the list is before the slot of the state.

The withdrawals of the list follow the queue before the step, in the order of the list.

The step then drops a prefix of that queue.

Each payment of the list is closed after the step.

A payment open after the step was open before it, or is at the slot of the state or later.

The slot of the state does not go back.

Unlike a release step, it does not keep the withdrawal of a payment open before and after it.

The chain of steps never reads that, and it would stop such steps from following each other. -/
structure PaymentStep (state after : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (released : List Slot) : Prop where
  nodup : released.Nodup
  queue : ∃ count, (after.builderPendingWithdrawals gloas).data.toList =
    ((state.builderPendingWithdrawals gloas).data.toList ++
      released.map (openWithdrawal state gloas)).drop count
  opened : ∀ slot ∈ released, PaymentOpen state gloas slot
  past : ∀ slot ∈ released, slot < state.slot
  closes : ∀ slot ∈ released, ¬ PaymentOpen after gloas slot
  noReopen : ∀ slot, PaymentOpen after gloas slot →
    PaymentOpen state gloas slot ∨ state.slot ≤ slot
  forward : state.slot ≤ after.slot

/-- A step that releases payments and closes each of them is such a step, with nothing dropped. -/
theorem PaymentStep.of_release {gloas : .glamsterdam ≤ fork} {released : List Slot}
    (release : PaymentRelease state after gloas released)
    (closes : ∀ slot ∈ released, ¬ PaymentOpen after gloas slot) :
    PaymentStep state after gloas released := by
  refine ⟨release.nodup, ⟨0, ?_⟩, release.opened, release.past, closes, release.noReopen,
    release.forward⟩
  simp [release.queue]

/-- A release, then a step that releases nothing, form one step.

The released payments must be closed after the second step.

That step may drop a prefix of the queue. -/
theorem PaymentStep.of_release_trans {gloas : .glamsterdam ≤ fork}
    {middle : BeaconState preset fork} {released : List Slot}
    (release : PaymentRelease state middle gloas released)
    (step : PaymentStep middle after gloas [])
    (closes : ∀ slot ∈ released, ¬ PaymentOpen after gloas slot) :
    PaymentStep state after gloas released := by
  obtain ⟨count, queue⟩ := step.queue
  refine ⟨release.nodup, ⟨count, ?_⟩, release.opened, release.past, closes, ?_,
    UInt64.le_trans release.forward step.forward⟩
  · rw [queue, release.queue]
    simp
  · intro slot open_after
    rcases step.noReopen slot open_after with open_middle | later
    · exact release.noReopen slot open_middle
    · exact Or.inr (UInt64.le_trans release.forward later)

/-- A payment closed before a step and older than its slot stays closed after the step. -/
theorem PaymentStep.keepsClosed {gloas : .glamsterdam ≤ fork} {released : List Slot}
    {slot : Slot} (step : PaymentStep state after gloas released)
    (closed : ¬ PaymentOpen state gloas slot) (past : slot < state.slot) :
    ¬ PaymentOpen after gloas slot := by
  intro open_after
  rcases step.noReopen slot open_after with open_before | later
  · exact closed open_before
  · exact absurd later (UInt64.not_le.mpr past)

/-- A step that releases payments, then a step that releases none, release those payments.

The second step may drop more of the queue, and it keeps each released payment closed. -/
theorem PaymentStep.trans_nil {gloas : .glamsterdam ≤ fork}
    {first second third : BeaconState preset fork} {released : List Slot}
    (one : PaymentStep first second gloas released) (two : PaymentStep second third gloas []) :
    PaymentStep first third gloas released := by
  obtain ⟨one_count, one_queue⟩ := one.queue
  obtain ⟨two_count, two_queue⟩ := two.queue
  refine ⟨one.nodup, ⟨one_count + two_count, ?_⟩, one.opened, one.past, ?_, ?_,
    UInt64.le_trans one.forward two.forward⟩
  · rw [two_queue, one_queue]
    simp [List.drop_drop]
  · exact fun slot mem => two.keepsClosed (one.closes slot mem)
      (UInt64.lt_of_lt_of_le (one.past slot mem) one.forward)
  · intro slot open_third
    rcases two.noReopen slot open_third with open_second | later
    · rcases one.noReopen slot open_second with open_first | later
      · exact Or.inl open_first
      · exact Or.inr later
    · exact Or.inr (UInt64.le_trans one.forward later)

/-- The withdrawals of a block release no payment, and drop a prefix of the queue. -/
theorem processWithdrawals_paymentStep {gloas : .glamsterdam ≤ fork}
    {capella : .shapella ≤ fork} {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) :
    PaymentStep state after gloas [] := by
  have inputs := payloadInputs_processWithdrawals computed
  have payments := processWithdrawals_payments gloas computed
  by_cases full : isParentBlockFull state gloas = true
  · obtain ⟨expected, -, applied, -⟩ := processWithdrawals_recorded gloas full computed
    have queue := (applyExpectedWithdrawals_builderQueues gloas applied).2
    have positions := slotPaymentPosition_congr inputs.slot
    have header : after.latestBlockHeader.slot = state.latestBlockHeader.slot := by
      rw [inputs.latestBlockHeader]
    have bid : after.latestExecutionPayloadBid gloas = state.latestExecutionPayloadBid gloas :=
      congrFun inputs.latestExecutionPayloadBid gloas
    have read : ∀ position,
        (paymentAt after gloas position).withdrawal = (paymentAt state gloas position).withdrawal :=
      fun position => by simp only [paymentAt, payments]
    refine ⟨List.nodup_nil, ⟨expected.processedBuilderWithdrawalsCount, ?_⟩, nofun, nofun,
      nofun, fun slot opened => Or.inl ((paymentOpen_congr positions header bid read slot).mp
        opened), by rw [inputs.slot]; exact UInt64.le_refl _⟩
    simpa using queue
  · have empty : isParentBlockFull state gloas = false := by simpa using full
    have same := processWithdrawals_of_parentEmpty (capella := capella) payload gloas empty
    rw [same] at computed
    cases computed
    exact .of_release (.refl state gloas) nofun

end EthLib.Consensus
