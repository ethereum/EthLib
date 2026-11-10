module

public import EthLib.Base.Proofs.MapM
public import EthLib.Consensus.Proofs.Accessors
public import EthLib.Consensus.Proofs.Transition.BuilderPayments
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

Other lemmas read the window after a write or a shift, and place a slot in it on natural numbers.

Two more facts on the window are stated here for the payment of each bid, and proved later.

A payment with weight has an amount, and the genesis epoch has an empty first half.

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

/-- Each pending payment with a positive weight has a positive amount. -/
def WeightedPaymentsFunded (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) :
    Prop :=
  ∀ position, 0 < (paymentAt state gloas position).weight →
    0 < (paymentAt state gloas position).withdrawal.amount

/-- In the genesis epoch, the first half of the window holds the payment of no bid.

That epoch is also the previous one, so the first half names no slot. -/
def GenesisFirstHalfEmpty (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) :
    Prop :=
  getCurrentEpoch state = GENESIS_EPOCH →
    ∀ position < preset.SLOTS_PER_EPOCH.toNat, paymentAt state gloas position = .empty

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

/-- A step that keeps the builder fields keeps each pending payment. -/
theorem BuilderFrame.paymentAt (frame : BuilderFrame state after) (gloas : .glamsterdam ≤ fork)
    (position : Nat) : paymentAt after gloas position = paymentAt state gloas position := by
  simp only [EthLib.Consensus.paymentAt, frame.payments]

/-- A move of both states to the same slot keeps a step that keeps the builder fields. -/
theorem BuilderFrame.withSlot (frame : BuilderFrame state after) (next : Slot) :
    BuilderFrame { state with slot := next } { after with slot := next } :=
  ⟨rfl, frame.headerSlot, frame.builders, frame.payments, frame.withdrawals, frame.bid⟩

/-- A step that keeps what the payments read, except that it may empty a payment.

It keeps the slot, the slot of the latest block, the latest bid and the queue.

At each position, the withdrawal of the payment stays, or has no amount after the step.

It may change the weights of the payments and the builders. -/
structure PaymentCancel (state after : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) :
    Prop where
  slot : after.slot = state.slot
  headerSlot : after.latestBlockHeader.slot = state.latestBlockHeader.slot
  bid : after.latestExecutionPayloadBid gloas = state.latestExecutionPayloadBid gloas
  withdrawals : after.builderPendingWithdrawals gloas = state.builderPendingWithdrawals gloas
  read : ∀ position,
    (paymentAt after gloas position).withdrawal = (paymentAt state gloas position).withdrawal ∨
      (paymentAt after gloas position).withdrawal.amount = 0

theorem PaymentCancel.refl (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) :
    PaymentCancel state state gloas :=
  ⟨rfl, rfl, rfl, rfl, fun _ => Or.inl rfl⟩

theorem PaymentCancel.trans {gloas : .glamsterdam ≤ fork}
    {first second third : BeaconState preset fork}
    (one : PaymentCancel first second gloas) (two : PaymentCancel second third gloas) :
    PaymentCancel first third gloas :=
  ⟨two.slot.trans one.slot, two.headerSlot.trans one.headerSlot, two.bid.trans one.bid,
    two.withdrawals.trans one.withdrawals, fun position => by
      rcases two.read position with same | empty
      · rcases one.read position with same' | empty'
        · exact Or.inl (same.trans same')
        · exact Or.inr (same ▸ empty')
      · exact Or.inr empty⟩

/-- A step that keeps the builder fields may only empty pending payments. -/
theorem PaymentCancel.of_frame {gloas : .glamsterdam ≤ fork} (frame : BuilderFrame state after) :
    PaymentCancel state after gloas :=
  ⟨frame.slot, frame.headerSlot, congrFun frame.bid gloas, congrFun frame.withdrawals gloas,
    fun position => Or.inl (by rw [frame.paymentAt gloas])⟩

/-- The position of the payment of each slot reads only the slot of the state. -/
theorem slotPaymentPosition_congr (same : after.slot = state.slot) (slot : Slot) :
    slotPaymentPosition after slot = slotPaymentPosition state slot := by
  unfold slotPaymentPosition getPreviousEpoch getCurrentEpoch
  rw [same]

/-- The position of the payment of each slot reads only the epoch of the state. -/
theorem slotPaymentPosition_congr_epoch
    (same : after.slot.toNat / preset.SLOTS_PER_EPOCH.toNat =
      state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat) (slot : Slot) :
    slotPaymentPosition after slot = slotPaymentPosition state slot := by
  have epoch : computeEpochAtSlot preset after.slot = computeEpochAtSlot preset state.slot := by
    apply UInt64.toNat_inj.mp
    simpa only [computeEpochAtSlot, UInt64.toNat_div] using same
  unfold slotPaymentPosition getPreviousEpoch getCurrentEpoch
  rw [epoch]

/-- The position of the parent payment reads only the slot and the slot of the latest block. -/
theorem parentPaymentPosition_congr (slot : after.slot = state.slot)
    (header : after.latestBlockHeader.slot = state.latestBlockHeader.slot) :
    parentPaymentPosition after = parentPaymentPosition state := by
  unfold parentPaymentPosition
  rw [header]
  exact slotPaymentPosition_congr slot _

/-- Whether the late path is open reads only the parent position and the withdrawals. -/
theorem latePaymentOpen_congr {gloas : .glamsterdam ≤ fork}
    (parent : parentPaymentPosition after = parentPaymentPosition state)
    (read : ∀ position,
      (paymentAt after gloas position).withdrawal = (paymentAt state gloas position).withdrawal) :
    latePaymentOpen after gloas = latePaymentOpen state gloas := by
  unfold latePaymentOpen
  rw [parent]
  split <;> simp only [read]

/-- A step that keeps the builder fields keeps the parent payment fresh. -/
theorem ParentPaymentFresh.of_frame {gloas : .glamsterdam ≤ fork}
    (frame : BuilderFrame state after) (fresh : ParentPaymentFresh state gloas) :
    ParentPaymentFresh after gloas := by
  intro position found
  simp only [frame.paymentAt gloas, latestBidWithdrawal, frame.bid]
  exact fresh position (parentPaymentPosition_congr frame.slot frame.headerSlot ▸ found)

/-- A step that keeps the builder fields keeps an amount for each payment with weight. -/
theorem WeightedPaymentsFunded.of_frame {gloas : .glamsterdam ≤ fork}
    (frame : BuilderFrame state after) (paid : WeightedPaymentsFunded state gloas) :
    WeightedPaymentsFunded after gloas := by
  intro position weighted
  rw [frame.paymentAt gloas] at weighted ⊢
  exact paid position weighted

/-- A step that keeps the builder fields keeps the first half of the genesis window empty. -/
theorem GenesisFirstHalfEmpty.of_frame {gloas : .glamsterdam ≤ fork}
    (frame : BuilderFrame state after) (genesis : GenesisFirstHalfEmpty state gloas) :
    GenesisFirstHalfEmpty after gloas := by
  intro genesisEpoch position early
  rw [frame.paymentAt gloas]
  exact genesis (by rwa [getCurrentEpoch, frame.slot] at genesisEpoch) position early

/-- The position of the payment of a slot on natural numbers.

The epoch must have one slot or more, and the window must fit in 64 bits.

A slot of the epoch of the state is in the second half.

A slot of the epoch before is in the first half.

Any other slot has no position. -/
theorem slotPaymentPosition_map_toNat
    (bounds : 1 ≤ preset.SLOTS_PER_EPOCH.toNat ∧ 2 * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64)
    (state : BeaconState preset fork) (slot : Slot) :
    (slotPaymentPosition state slot).map UInt64.toNat =
      if slot.toNat / preset.SLOTS_PER_EPOCH.toNat =
          state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat then
        some (preset.SLOTS_PER_EPOCH.toNat + slot.toNat % preset.SLOTS_PER_EPOCH.toNat)
      else if slot.toNat / preset.SLOTS_PER_EPOCH.toNat =
          state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat - 1 then
        some (slot.toNat % preset.SLOTS_PER_EPOCH.toNat)
      else none := by
  obtain ⟨one, small⟩ := bounds
  have current : computeEpochAtSlot preset slot = getCurrentEpoch state ↔
      slot.toNat / preset.SLOTS_PER_EPOCH.toNat =
        state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    rw [← UInt64.toNat_inj, getCurrentEpoch_toNat, computeEpochAtSlot, UInt64.toNat_div]
  have previous : computeEpochAtSlot preset slot = getPreviousEpoch state ↔
      slot.toNat / preset.SLOTS_PER_EPOCH.toNat =
        state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat - 1 := by
    rw [← UInt64.toNat_inj, getPreviousEpoch_toNat, getCurrentEpoch_toNat, computeEpochAtSlot,
      UInt64.toNat_div]
  have offset : (slot % preset.SLOTS_PER_EPOCH).toNat =
      slot.toNat % preset.SLOTS_PER_EPOCH.toNat := UInt64.toNat_mod _ _
  have below := Nat.mod_lt slot.toNat one
  unfold slotPaymentPosition
  simp only [current, previous]
  split
  · simp only [Option.map_some, UInt64.toNat_add, offset, Option.some.injEq]
    exact Nat.mod_eq_of_lt (by omega)
  · split <;> simp [offset]

/-- Two slots with the same position of their payment are the same slot.

The epoch must have one slot or more, and the window must fit in 64 bits. -/
theorem slotPaymentPosition_injective
    (bounds : 1 ≤ preset.SLOTS_PER_EPOCH.toNat ∧ 2 * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64)
    {first second : Slot} {position : UInt64}
    (atFirst : slotPaymentPosition state first = some position)
    (atSecond : slotPaymentPosition state second = some position) : first = second := by
  have firstNat := slotPaymentPosition_map_toNat bounds state first
  have secondNat := slotPaymentPosition_map_toNat bounds state second
  rw [atFirst] at firstNat
  rw [atSecond] at secondNat
  have firstSplit := Nat.div_add_mod first.toNat preset.SLOTS_PER_EPOCH.toNat
  have secondSplit := Nat.div_add_mod second.toNat preset.SLOTS_PER_EPOCH.toNat
  have firstBelow := Nat.mod_lt first.toNat bounds.1
  have secondBelow := Nat.mod_lt second.toNat bounds.1
  apply UInt64.toNat_inj.mp
  simp only [Option.map_some] at firstNat secondNat
  split at firstNat <;> split at secondNat <;> (try split at firstNat) <;>
    (try split at secondNat) <;>
    simp only [Option.some.injEq, reduceCtorEq] at firstNat secondNat <;> grind

/-- A read of the pending payments inside the window is the read of their elements. -/
theorem paymentAt_of_lt {gloas : .glamsterdam ≤ fork} {position : Nat}
    (inside : position < 2 * preset.SLOTS_PER_EPOCH.toNat) :
    paymentAt state gloas position = (state.builderPendingPayments gloas)[position] := by
  simp [paymentAt, inside]
  rfl

/-- The released withdrawals are those of the positions of the first epoch that reach the quorum.

They follow the order of the positions. -/
theorem releasedPayments_eq_map (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (quorum : Gwei) :
    releasedPayments (state.builderPendingPayments gloas).elements.toList
        preset.SLOTS_PER_EPOCH.toNat quorum =
      ((List.range preset.SLOTS_PER_EPOCH.toNat).filter
          fun position => decide (quorum ≤ (paymentAt state gloas position).weight)).map
        fun position => (paymentAt state gloas position).withdrawal := by
  have take : (state.builderPendingPayments gloas).elements.toList.take
      preset.SLOTS_PER_EPOCH.toNat =
      (List.range preset.SLOTS_PER_EPOCH.toNat).map (paymentAt state gloas) := by
    apply List.ext_getElem (by simp; omega)
    intro position inside _
    simp only [List.length_take, Vector.length_toList] at inside
    rw [List.getElem_take, Vector.getElem_toList, List.getElem_map, List.getElem_range,
      paymentAt_of_lt (by omega)]
    rfl
  unfold releasedPayments
  rw [take, List.filter_map, List.map_map]
  rfl

/-- A write at one position of the pending payments puts the entry there.

Every other position keeps its payment. -/
theorem paymentAt_set {gloas : .glamsterdam ≤ fork} {k : Nat} {entry : BuilderPendingPayment}
    {inside : k < 2 * preset.SLOTS_PER_EPOCH.toNat}
    (payments : after.builderPendingPayments gloas =
      (state.builderPendingPayments gloas).set k entry inside) (position : Nat) :
    paymentAt after gloas position =
      if position = k then entry else paymentAt state gloas position := by
  unfold paymentAt
  rw [payments, Serialization.Ssz.RootedVector.elements_set, Vector.getElem?_set]
  split <;> rename_i same
  · subst same
    simp
  · simp [Ne.symm same]

/-- The payments move by one epoch.

A position of the first epoch then takes the payment one epoch later. -/
theorem paymentAt_shiftPayments_early {gloas : .glamsterdam ≤ fork} {position : Nat}
    (payments : after.builderPendingPayments gloas =
      shiftPayments (state.builderPendingPayments gloas))
    (early : position < preset.SLOTS_PER_EPOCH.toNat) :
    paymentAt after gloas position =
      paymentAt state gloas (position + preset.SLOTS_PER_EPOCH.toNat) := by
  rw [paymentAt_of_lt (by omega), paymentAt_of_lt (by omega)]
  simp only [payments]
  exact getElem_shiftPayments_early _ early

/-- The payments move by one epoch.

Each position from one epoch on then holds the payment of no bid. -/
theorem paymentAt_shiftPayments_late {gloas : .glamsterdam ≤ fork} {position : Nat}
    (payments : after.builderPendingPayments gloas =
      shiftPayments (state.builderPendingPayments gloas))
    (late : preset.SLOTS_PER_EPOCH.toNat ≤ position) :
    paymentAt after gloas position = .empty := by
  by_cases inside : position < 2 * preset.SLOTS_PER_EPOCH.toNat
  · rw [paymentAt_of_lt inside]
    simp only [payments]
    exact getElem_shiftPayments_late _ late inside
  · simp [paymentAt, Nat.not_lt.mp inside]

/-- A step that keeps the builder fields and the parent payment position keeps the invariant.

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
