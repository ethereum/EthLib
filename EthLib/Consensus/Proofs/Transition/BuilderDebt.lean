module

public import EthLib.Base.Proofs.MapM
public import EthLib.Consensus.Transition.ParentPayload
public import EthLib.Consensus.Transition.Payload

/-!
# Proofs: the debt of each builder stays within its balance

From Gloas a builder owes its queued withdrawals and the payments of its bids.

A bid passes only if the balance of its builder covers the bid, that debt and a minimum.

The invariant here says that the balance always covers the debt.

With it, no withdrawal of a builder falls short.

The payment of the parent block can leave the pending payments with no block between.

That happens when the parent is older than the previous epoch.

The child then queues the value of the parent bid, by the late path of the parent payload.

So the invariant also reserves that value, from when the payment leaves until the child comes.

It reserves it too when the slashing of the proposer cancelled the payment.

The late path reads the bid, and not the payment.

The invariant has four parts.

* For each builder, the debt plus the reserved value is at most the balance.
* In the window, the parent payment has no weight, and it pays the latest bid or has no amount.
* A builder that has started to exit owes nothing and has no reserved value.
* Each position of the window after that of the parent holds the payment of no bid.

The second part makes the first one last across an epoch.

With a positive quorum, the epoch step drops a payment with no weight instead of paying it.

The value of that payment then moves from the debt to the reserve.

The third part covers the sweep of builders, which pays a withdrawable builder its whole balance.

The fourth part keeps the second one true after a block whose bid has no value.

Such a bid records no payment, so the position of the block keeps what it held.

The proofs that follow show that blocks and slots keep it, not each step inside them.

Inside a block, the settled parent payment and the reserve both count the same value until the bid.

Most steps keep the builders, their payments, their withdrawals and the latest bid.

Such a step keeps the invariant if it also keeps the slot and the slot of the latest block.

[EIP-7732] adds the builders, their bids and their payments.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-- The balance of a builder on natural numbers, and zero for an index past the registry. -/
def builderBalance (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (index : BuilderIndex) : Nat :=
  match (state.builders gloas).data[index.toNat]? with
  | some builder => builder.balance.toNat
  | none => 0

/-- The pending payment at a position, and the payment of no bid past the window. -/
def paymentAt (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) (position : Nat) :
    BuilderPendingPayment :=
  ((state.builderPendingPayments gloas).elements[position]?).getD .empty

/-- Whether the invariant reserves the value of the latest bid.

It does when the payment of the parent has left the window, or when that payment has no amount. -/
def latePaymentOpen (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) : Bool :=
  match parentPaymentPosition state with
  | none => true
  | some position => (paymentAt state gloas position.toNat).withdrawal.amount == 0

/-- The value that the invariant reserves for a builder, for the late path.

It is the value of the latest bid when the builder made it and the reserve is open.

It is zero otherwise. -/
def lateBidValue (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (index : BuilderIndex) : Nat :=
  let bid := state.latestExecutionPayloadBid gloas
  if bid.builderIndex = index ∧ latePaymentOpen state gloas = true then bid.value.toNat else 0

/-- The withdrawal that pays the latest bid, as the bid step records it for any proposer. -/
def latestBidWithdrawal (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) :
    BuilderPendingWithdrawal :=
  (bidPayment (state.latestExecutionPayloadBid gloas) 0).withdrawal

/-- The payment of the parent, while it is in the window, has no weight.

It pays the latest bid, or it has no amount. -/
def ParentPaymentFresh (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) : Prop :=
  ∀ position, parentPaymentPosition state = some position →
    (paymentAt state gloas position.toNat).weight = 0 ∧
      ((paymentAt state gloas position.toNat).withdrawal.amount = 0 ∨
        (paymentAt state gloas position.toNat).withdrawal = latestBidWithdrawal state gloas)

/-- Each position after that of the parent holds the payment of no bid.

Every position is after it when the parent payment has left the window. -/
def LaterPaymentsEmpty (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) : Prop :=
  ∀ position, (∀ parent, parentPaymentPosition state = some parent → parent.toNat < position) →
    paymentAt state gloas position = .empty

/-- From Gloas: the balance of each builder covers what it owes and what the late path may add.

A builder that has started to exit owes nothing, and the late path adds nothing for it.

While the payment of the parent is in the window, it has no weight.

It then pays the latest bid or has no amount.

Each position after it holds the payment of no bid. -/
structure BuilderDebtCovered (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) :
    Prop where
  covered : ∀ index,
    pendingBuilderTotal state gloas index + lateBidValue state gloas index ≤
      builderBalance state gloas index
  exitedClear : ∀ index builder, (state.builders gloas).data[index.toNat]? = some builder →
    builder.withdrawableEpoch ≠ FAR_FUTURE_EPOCH →
      pendingBuilderTotal state gloas index + lateBidValue state gloas index = 0
  parentFresh : ParentPaymentFresh state gloas
  laterEmpty : LaterPaymentsEmpty state gloas

/-- A step that keeps the builders, their payments, their withdrawals and the latest bid.

It also keeps the slot and the slot of the latest block, which place the parent payment. -/
structure BuilderFrame (state after : BeaconState preset fork) : Prop where
  slot : after.slot = state.slot
  headerSlot : after.latestBlockHeader.slot = state.latestBlockHeader.slot
  builders : after.builders = state.builders
  payments : after.builderPendingPayments = state.builderPendingPayments
  withdrawals : after.builderPendingWithdrawals = state.builderPendingWithdrawals
  bid : after.latestExecutionPayloadBid = state.latestExecutionPayloadBid

theorem BuilderFrame.refl (state : BeaconState preset fork) : BuilderFrame state state :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem BuilderFrame.trans {first second third : BeaconState preset fork}
    (one : BuilderFrame first second) (two : BuilderFrame second third) :
    BuilderFrame first third :=
  ⟨two.slot.trans one.slot, two.headerSlot.trans one.headerSlot,
    two.builders.trans one.builders, two.payments.trans one.payments,
    two.withdrawals.trans one.withdrawals, two.bid.trans one.bid⟩

theorem BuilderFrame.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (frame : ∀ s x s', step s x = .ok s' → BuilderFrame s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : BuilderFrame state after :=
  foldlM_ok_invariant (BuilderFrame state)
    (fun _ _ _ before ok => before.trans (frame _ _ _ ok)) (BuilderFrame.refl state) computed

/-- The position of the parent payment reads only the slot and the slot of the latest block. -/
theorem parentPaymentPosition_congr (slot : after.slot = state.slot)
    (header : after.latestBlockHeader.slot = state.latestBlockHeader.slot) :
    parentPaymentPosition after = parentPaymentPosition state := by
  unfold parentPaymentPosition getPreviousEpoch getCurrentEpoch
  rw [slot, header]

/-- A read of the pending payments inside the window is the read of their elements. -/
theorem paymentAt_of_lt {gloas : .glamsterdam ≤ fork} {position : Nat}
    (inside : position < 2 * preset.SLOTS_PER_EPOCH.toNat) :
    paymentAt state gloas position = (state.builderPendingPayments gloas)[position] := by
  simp [paymentAt, inside]
  rfl

/-- A step that keeps the builder fields and the position of the parent payment keeps the
invariant.

The invariant reads nothing else of the state. -/
theorem BuilderDebtCovered.of_position {gloas : .glamsterdam ≤ fork}
    (position : parentPaymentPosition after = parentPaymentPosition state)
    (builders : after.builders = state.builders)
    (payments : after.builderPendingPayments = state.builderPendingPayments)
    (withdrawals : after.builderPendingWithdrawals = state.builderPendingWithdrawals)
    (bid : after.latestExecutionPayloadBid = state.latestExecutionPayloadBid)
    (holds : BuilderDebtCovered state gloas) : BuilderDebtCovered after gloas := by
  have total : ∀ index,
      pendingBuilderTotal after gloas index = pendingBuilderTotal state gloas index :=
    fun _ => by simp only [pendingBuilderTotal, payments, withdrawals]
  have opened : latePaymentOpen after gloas = latePaymentOpen state gloas := by
    simp only [latePaymentOpen, paymentAt, position, payments]
  have late : ∀ index, lateBidValue after gloas index = lateBidValue state gloas index :=
    fun _ => by simp only [lateBidValue, opened, bid]
  have balance : ∀ index, builderBalance after gloas index = builderBalance state gloas index :=
    fun _ => by simp only [builderBalance, builders]
  refine ⟨fun index => ?_, fun index builder found exited => ?_, fun p found => ?_,
    fun k later => ?_⟩
  · rw [total, late, balance]
    exact holds.covered index
  · rw [total, late]
    exact holds.exitedClear index builder (by rwa [builders] at found) exited
  · simp only [paymentAt, latestBidWithdrawal, payments, bid]
    exact holds.parentFresh p (position ▸ found)
  · simp only [paymentAt, payments]
    exact holds.laterEmpty k fun parent found => later parent (position ▸ found)

/-- A step that keeps the builder fields and the two slots of its frame keeps the invariant. -/
theorem BuilderDebtCovered.of_frame {gloas : .glamsterdam ≤ fork}
    (frame : BuilderFrame state after) (holds : BuilderDebtCovered state gloas) :
    BuilderDebtCovered after gloas :=
  .of_position (parentPaymentPosition_congr frame.slot frame.headerSlot) frame.builders
    frame.payments frame.withdrawals frame.bid holds

end EthLib.Consensus
