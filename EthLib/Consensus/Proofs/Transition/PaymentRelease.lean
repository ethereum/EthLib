module

public import EthLib.Consensus.Proofs.Time
public import EthLib.Consensus.Proofs.Transition.BuilderDebt
public import EthLib.Consensus.Proofs.Transition.ParentPayload

/-!
# Proofs: the steps that pay the bid of a block

From Gloas the builder of a block pays its proposer through a pending payment.

A bid is named by the slot of its block, since the slots of the blocks of a chain increase.

The payment of a bid is open while it may still be paid, as the state shows.

It is open while the window holds its payment with a positive amount.

It is also open when its block is the latest one, the late path may pay it, and it has a value.

The latest bid must then be the bid of that block.

Three paths queue the withdrawal of an open payment.

* A child that builds on the full parent settles the payment of the parent.
* The epoch step pays each payment of the previous epoch that reaches the quorum.
* A child of a parent whose payment left the window queues the value of the parent bid.

The first and the third are the payment of the parent, and the second is the epoch step.

Each step lemma here has the same shape, which a structure names.

The queue gains the withdrawals of a list of open payments, with no slot twice.

A payment closed before the step opens only at the slot of the state or later.

So a payment of an earlier slot that is closed before the step stays closed after it.

The epoch step also closes each payment that it pays.

It pays each payment of the previous epoch that reaches the quorum.

The payment of the parent closes the payment in the window.

The parent slot may stay open through the late path, until the header moves to the new block.

A later step shows that the header step closes it.

[EIP-7732] adds the builders, their bids and their payments.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-- Whether the window holds the payment of the block at a slot, with a positive amount. -/
def PaymentInWindow (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (slot : Slot) : Prop :=
  ∃ position, slotPaymentPosition state slot = some position ∧
    0 < (paymentAt state gloas position.toNat).withdrawal.amount

/-- Whether the payment of the bid of the block at a slot may still be paid.

It is open while the window holds that payment with a positive amount.

It is also open when the block is the latest one and the latest bid is its bid.

The late path must then be open, and the bid must have a value. -/
def PaymentOpen (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) (slot : Slot) :
    Prop :=
  PaymentInWindow state gloas slot ∨
    (slot = state.latestBlockHeader.slot ∧ (state.latestExecutionPayloadBid gloas).slot = slot ∧
      latePaymentOpen state gloas = true ∧ 0 < (state.latestExecutionPayloadBid gloas).value)

/-- The withdrawal that pays the bid of the block at a slot.

It is the payment in the window, if the window holds it with a positive amount.

Otherwise it is the withdrawal of the latest bid, which the late path queues.

It is read only for an open payment. -/
def openWithdrawal (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (slot : Slot) : BuilderPendingWithdrawal :=
  match slotPaymentPosition state slot with
  | some position =>
    let payment := paymentAt state gloas position.toNat
    if 0 < payment.withdrawal.amount then payment.withdrawal else latestBidWithdrawal state gloas
  | none => latestBidWithdrawal state gloas

/-- A step that queues the withdrawals of a list of open payments, with no slot twice.

The withdrawals follow the queue before the step, in the order of the list.

Each slot of the list is before the slot of the state.

A payment open after the step was open before it, or is at the slot of the state or later.

A payment open before and after the step is paid by the same withdrawal.

The slot of the state does not go back. -/
structure PaymentRelease (state after : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (released : List Slot) : Prop where
  nodup : released.Nodup
  queue : (after.builderPendingWithdrawals gloas).data.toList =
    (state.builderPendingWithdrawals gloas).data.toList ++
      released.map (openWithdrawal state gloas)
  opened : ∀ slot ∈ released, PaymentOpen state gloas slot
  past : ∀ slot ∈ released, slot < state.slot
  noReopen : ∀ slot, PaymentOpen after gloas slot →
    PaymentOpen state gloas slot ∨ state.slot ≤ slot
  stable : ∀ slot, PaymentOpen after gloas slot → PaymentOpen state gloas slot →
    openWithdrawal after gloas slot = openWithdrawal state gloas slot
  forward : state.slot ≤ after.slot

/-- The withdrawal of the latest bid reads only the latest bid. -/
theorem latestBidWithdrawal_congr {gloas : .glamsterdam ≤ fork}
    (bid : after.latestExecutionPayloadBid gloas = state.latestExecutionPayloadBid gloas) :
    latestBidWithdrawal after gloas = latestBidWithdrawal state gloas := by
  simp only [latestBidWithdrawal, bid]

/-- A step that keeps what the payments read releases no payment.

It keeps the position of each slot, the slot of the latest block, the latest bid and the queue.

It keeps the withdrawal of each pending payment, and its slot does not go back. -/
theorem PaymentRelease.of_fields {gloas : .glamsterdam ≤ fork}
    (forward : state.slot ≤ after.slot)
    (positions : ∀ slot, slotPaymentPosition after slot = slotPaymentPosition state slot)
    (header : after.latestBlockHeader.slot = state.latestBlockHeader.slot)
    (bid : after.latestExecutionPayloadBid gloas = state.latestExecutionPayloadBid gloas)
    (read : ∀ position,
      (paymentAt after gloas position).withdrawal = (paymentAt state gloas position).withdrawal)
    (withdrawals :
      after.builderPendingWithdrawals gloas = state.builderPendingWithdrawals gloas) :
    PaymentRelease state after gloas [] := by
  have parent : parentPaymentPosition after = parentPaymentPosition state := by
    unfold parentPaymentPosition
    rw [header]
    exact positions _
  have late : latePaymentOpen after gloas = latePaymentOpen state gloas := by
    simp only [latePaymentOpen, parent, read]
  have opens : ∀ slot, PaymentOpen after gloas slot ↔ PaymentOpen state gloas slot := by
    intro slot
    simp only [PaymentOpen, PaymentInWindow, positions, read, header, bid, late]
  have same : ∀ slot, openWithdrawal after gloas slot = openWithdrawal state gloas slot := by
    intro slot
    simp only [openWithdrawal, positions, read, latestBidWithdrawal_congr bid]
  exact ⟨List.nodup_nil, by simp [withdrawals], by simp, by simp,
    fun slot opened => Or.inl ((opens slot).mp opened), fun slot _ _ => same slot, forward⟩

/-- A step that keeps the builder fields releases no payment. -/
theorem PaymentRelease.of_frame {gloas : .glamsterdam ≤ fork} (frame : BuilderFrame state after) :
    PaymentRelease state after gloas [] :=
  .of_fields (frame.slot.symm ▸ UInt64.le_refl _) (slotPaymentPosition_congr frame.slot)
    frame.headerSlot
    (congrFun frame.bid gloas)
    (fun position => by simp only [paymentAt, frame.payments])
    (congrFun frame.withdrawals gloas)

/-- A state releases no payment to itself. -/
theorem PaymentRelease.refl (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) :
    PaymentRelease state state gloas [] :=
  .of_frame (.refl state)

/-- A slot at the position of the parent payment is paid by the withdrawal of the latest bid.

The parent payment must have no weight, and pay the latest bid or have no amount. -/
theorem openWithdrawal_eq_latestBidWithdrawal {gloas : .glamsterdam ≤ fork}
    (fresh : ParentPaymentFresh state gloas) {slot : Slot}
    (atParent : slotPaymentPosition state slot = parentPaymentPosition state) :
    openWithdrawal state gloas slot = latestBidWithdrawal state gloas := by
  unfold openWithdrawal
  rw [atParent]
  cases located : parentPaymentPosition state with
  | none => rfl
  | some p =>
    dsimp only
    by_cases amount : 0 < (paymentAt state gloas p.toNat).withdrawal.amount
    · rw [ite_eq_left_of_eq_true _ _ (eq_true amount)]
      rcases (fresh p located).2 with zero | settles
      · rw [zero] at amount
        exact absurd amount (by decide)
      · exact settles
    · rw [ite_eq_right_of_eq_false _ _ (eq_false amount)]

/-- The late path is open when the window does not hold the parent payment with a positive amount.
-/
theorem latePaymentOpen_of_not_paymentInWindow {gloas : .glamsterdam ≤ fork}
    (window : ¬ PaymentInWindow state gloas state.latestBlockHeader.slot) :
    latePaymentOpen state gloas = true := by
  unfold latePaymentOpen parentPaymentPosition
  cases located : slotPaymentPosition state state.latestBlockHeader.slot with
  | none => rfl
  | some p =>
    simp only [beq_iff_eq]
    exact UInt64.le_zero_iff.mp (UInt64.not_lt.mp fun pos => window ⟨p, located, pos⟩)

/-- With the latest bid at the slot of the latest block and a positive value, that slot is open. -/
theorem paymentOpen_latestBlock {gloas : .glamsterdam ≤ fork}
    (bidSlot : (state.latestExecutionPayloadBid gloas).slot = state.latestBlockHeader.slot)
    (value : 0 < (state.latestExecutionPayloadBid gloas).value) :
    PaymentOpen state gloas state.latestBlockHeader.slot := by
  by_cases window : PaymentInWindow state gloas state.latestBlockHeader.slot
  · exact Or.inl window
  · exact Or.inr ⟨rfl, bidSlot, latePaymentOpen_of_not_paymentInWindow window, value⟩

/-- The payment of the parent queues at most the withdrawal of the parent's slot, if it is open.

The parent must be older than the slot of the state, as it is when the parent payload runs.

The latest bid must be at the slot of the parent, as it is then too.

Those two hypotheses are assumptions, which a later step proves.

The parent payment must also have no weight, and pay the latest bid or have no amount.

That one is part of the builder debt invariant.

It queues it when the window holds it with a positive amount, or has left it with the bid open.

After the step, the window does not hold the payment of the parent with a positive amount.

The parent slot may stay open through the late path, until the header moves. -/
theorem settleParentPayment_release {gloas : .glamsterdam ≤ fork}
    (older : state.latestBlockHeader.slot < state.slot)
    (fresh : ParentPaymentFresh state gloas)
    (bidMatches : (state.latestExecutionPayloadBid gloas).slot = state.latestBlockHeader.slot)
    (computed : settleParentPayment state gloas = .ok after) :
    ∃ released : List Slot, PaymentRelease state after gloas released ∧
      released.Sublist [state.latestBlockHeader.slot] ∧
      (PaymentInWindow state gloas state.latestBlockHeader.slot ∨
          (slotPaymentPosition state state.latestBlockHeader.slot = none ∧
            PaymentOpen state gloas state.latestBlockHeader.slot) →
        released = [state.latestBlockHeader.slot]) ∧
      ¬ PaymentInWindow after gloas state.latestBlockHeader.slot := by
  have same := settleParentPayment_eq computed
  have headerEq : after.latestBlockHeader = state.latestBlockHeader := by rw [same]
  have bidEq : after.latestExecutionPayloadBid = state.latestExecutionPayloadBid := by rw [same]
  have slotEq : after.slot = state.slot := by rw [same]
  have forward : state.slot ≤ after.slot := by rw [slotEq]; exact UInt64.le_refl _
  have positions := slotPaymentPosition_congr slotEq
  unfold settleParentPayment at computed
  split at computed
  · rename_i index parent
    have settled := liftAccessor_ok.mp computed
    obtain ⟨inRange, payments, queue⟩ := settleBuilderPayment_spec settled
    have read := paymentAt_set payments
    rw [← paymentAt_of_lt inRange] at queue
    have atParent : slotPaymentPosition state state.latestBlockHeader.slot = some index := parent
    have closed : ¬ PaymentInWindow after gloas state.latestBlockHeader.slot := by
      rintro ⟨position, found, positive⟩
      rw [positions, atParent] at found
      cases found
      simp only [read, ↓reduceIte] at positive
      exact absurd positive (by decide)
    have bidWithdrawal := latestBidWithdrawal_congr (congrFun bidEq gloas)
    refine ⟨if 0 < (paymentAt state gloas index.toNat).withdrawal.amount then
      [state.latestBlockHeader.slot] else [], ⟨?_, ?_, ?_, ?_, ?_, ?_, forward⟩, ?_, ?_, closed⟩
    · split <;> simp
    · rw [queue]
      split <;> rename_i positive <;> simp [openWithdrawal, atParent, positive]
    · intro slot member
      split at member
      · rename_i positive
        rw [List.mem_singleton] at member
        subst member
        exact Or.inl ⟨index, atParent, positive⟩
      · cases member
    · intro slot member
      split at member
      · rw [List.mem_singleton] at member
        exact member ▸ older
      · cases member
    · rintro slot (⟨position, found, positive⟩ | ⟨atHeader, bidSlot, -, value⟩)
      · rw [positions] at found
        rw [read] at positive
        split at positive
        · exact absurd positive (by decide)
        · exact Or.inl (Or.inl ⟨position, found, positive⟩)
      · rw [headerEq] at atHeader
        rw [bidEq] at value bidSlot
        subst atHeader
        exact Or.inl (paymentOpen_latestBlock bidSlot value)
    · intro slot _ _
      by_cases atIndex : slotPaymentPosition state slot = some index
      · rw [openWithdrawal_eq_latestBidWithdrawal fresh (atIndex.trans parent.symm),
          ← bidWithdrawal]
        simp only [openWithdrawal, positions, atIndex, read, ↓reduceIte,
          BuilderPendingPayment.empty]
        rfl
      · unfold openWithdrawal
        rw [positions, bidWithdrawal]
        cases position : slotPaymentPosition state slot with
        | none => rfl
        | some p =>
          have other : p.toNat ≠ index.toNat := fun same =>
            atIndex (position.trans (congrArg some (UInt64.toNat_inj.mp same)))
          simp only [read, other, ↓reduceIte]
    · split <;> simp
    · rintro (⟨position, found, positive⟩ | ⟨missing, -⟩)
      · rw [atParent] at found
        cases found
        simp [positive]
      · rw [atParent] at missing
        cases missing
  · rename_i parent
    have atParent : slotPaymentPosition state state.latestBlockHeader.slot = none := parent
    dsimp only at computed
    split at computed
    · rename_i valued
      cases computed
      refine ⟨[state.latestBlockHeader.slot], ⟨by simp, ?_, ?_,
        fun _ member => List.mem_singleton.mp member ▸ older, fun _ opened => Or.inl opened,
        fun _ _ _ => rfl, forward⟩, List.Sublist.refl _, fun _ => rfl, ?_⟩
      · simp [openWithdrawal, atParent, latestBidWithdrawal, bidPayment]
      · intro slot member
        rw [List.mem_singleton] at member
        subst member
        exact Or.inr ⟨rfl, bidMatches, by simp [latePaymentOpen, parent], valued⟩
      · rintro ⟨position, found, -⟩
        rw [positions, atParent] at found
        cases found
    · rename_i valueless
      cases computed
      refine ⟨[], ⟨List.nodup_nil, by simp, by simp, by simp, fun _ opened => Or.inl opened,
        fun _ _ _ => rfl, forward⟩, List.nil_sublist _, ?_, ?_⟩
      · rintro (⟨position, found, -⟩ | ⟨-, ⟨position, found, -⟩ | ⟨-, -, -, value⟩⟩)
        · rw [atParent] at found
          cases found
        · rw [atParent] at found
          cases found
        · exact absurd value valueless
      · rintro ⟨position, found, -⟩
        rw [atParent] at found
        cases found

/-- With a positive quorum, the epoch step of the payments queues the withdrawals of open payments.

The positive quorum is an assumption on the preset, which both presets meet.

The state after the step is read at the next slot, the first of the next epoch.

The slots it pays are distinct, and each payment it pays is closed after it.

It pays each payment of the previous epoch whose weight is at least the quorum that it computes.

The hypothesis on the parent payment is part of the builder debt invariant.

The hypotheses on the weights and the genesis epoch are assumptions, which a later step proves.
-/
theorem processBuilderPendingPayments_release (positive : preset.PaymentQuorumPositive)
    {gloas : .glamsterdam ≤ fork} (fresh : ParentPaymentFresh state gloas)
    (paid : WeightedPaymentsFunded state gloas) (genesis : GenesisFirstHalfEmpty state gloas)
    (computed : processBuilderPendingPayments state gloas = .ok after) {next : Slot}
    (advance : next.toNat = state.slot.toNat + 1) (first : next % preset.SLOTS_PER_EPOCH = 0) :
    ∃ quorum, ∃ released : List Slot, getBuilderPaymentQuorumThreshold state = .ok quorum ∧
      PaymentRelease state { after with slot := next } gloas released ∧
      (∀ slot ∈ released, ¬ PaymentOpen { after with slot := next } gloas slot) ∧
      (∀ slot position, slotPaymentPosition state slot = some position →
        position.toNat < preset.SLOTS_PER_EPOCH.toNat →
        quorum ≤ (paymentAt state gloas position.toNat).weight → slot ∈ released) := by
  have bounds := positive.slotsPerEpoch_bounds
  have one := bounds.1
  obtain ⟨quorum, found, queue, shifted⟩ := processBuilderPendingPayments_spec computed
  have least := getBuilderPaymentQuorumThreshold_pos positive found
  have same := processBuilderPendingPayments_eq computed
  have movedHeader : ({ after with slot := next }).latestBlockHeader = state.latestBlockHeader := by
    rw [same]
  have movedBid : ({ after with slot := next }).latestExecutionPayloadBid =
      state.latestExecutionPayloadBid := by
    rw [same]
  have movedSlot : ({ after with slot := next }).slot = next := rfl
  have movedPayments : ({ after with slot := next }).builderPendingPayments gloas =
      shiftPayments (state.builderPendingPayments gloas) := shifted
  have movedQueue : (({ after with slot := next }).builderPendingWithdrawals gloas).data.toList =
      (state.builderPendingWithdrawals gloas).data.toList ++
        releasedPayments (state.builderPendingPayments gloas).elements.toList
          preset.SLOTS_PER_EPOCH.toNat quorum := queue
  generalize { after with slot := next } = moved at *
  -- The next slot starts the epoch after the current one.
  have movedEpoch : moved.slot.toNat / preset.SLOTS_PER_EPOCH.toNat =
      state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 := by
    rw [movedSlot]
    exact nextSlot_epoch_of_boundary advance first
  have before := slotPaymentPosition_map_toNat bounds state
  have afterPosition := slotPaymentPosition_map_toNat bounds moved
  simp only [movedEpoch, Nat.add_sub_cancel] at afterPosition
  have early := fun j => paymentAt_shiftPayments_early (position := j) movedPayments
  have beyond := fun j => paymentAt_shiftPayments_late (position := j) movedPayments
  have weighted : ∀ i, i < preset.SLOTS_PER_EPOCH.toNat →
      quorum ≤ (paymentAt state gloas i).weight →
      state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≠ 0 ∧
        0 < (paymentAt state gloas i).withdrawal.amount := by
    intro i inside reached
    refine ⟨fun zero => ?_, paid i (UInt64.lt_of_lt_of_le least reached)⟩
    have genesisEpoch : getCurrentEpoch state = GENESIS_EPOCH := by
      apply UInt64.toNat_inj.mp
      rw [getCurrentEpoch_toNat, zero]
      rfl
    rw [genesis genesisEpoch i inside] at reached
    exact absurd (UInt64.lt_of_lt_of_le least reached) (by decide)
  have mulLe := Nat.div_mul_le_self state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
  have slotSmall := state.slot.toNat_lt
  generalize state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat = epoch
    at before afterPosition weighted mulLe
  -- After the genesis epoch, the epoch before ends where the epoch of the state starts.
  have step : epoch ≠ 0 → (epoch - 1) * preset.SLOTS_PER_EPOCH.toNat +
      preset.SLOTS_PER_EPOCH.toNat = epoch * preset.SLOTS_PER_EPOCH.toNat := fun nonzero => by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.pos_of_ne_zero nonzero)]
  have fits : ∀ i, i < preset.SLOTS_PER_EPOCH.toNat →
      i + (epoch - 1) * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 := by
    intro i inside
    by_cases zero : epoch = 0
    · subst zero
      simp only [Nat.zero_sub, Nat.zero_mul, Nat.add_zero]
      omega
    · have := step zero
      omega
  have slotNat : ∀ i, i < preset.SLOTS_PER_EPOCH.toNat →
      (UInt64.ofNat (i + (epoch - 1) * preset.SLOTS_PER_EPOCH.toNat)).toNat =
        i + (epoch - 1) * preset.SLOTS_PER_EPOCH.toNat :=
    fun i inside => UInt64.toNat_ofNat_of_lt' (fits i inside)
  have slotEpoch : ∀ i, i < preset.SLOTS_PER_EPOCH.toNat →
      (UInt64.ofNat (i + (epoch - 1) * preset.SLOTS_PER_EPOCH.toNat)).toNat /
        preset.SLOTS_PER_EPOCH.toNat = epoch - 1 := by
    intro i inside
    rw [slotNat i inside, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt inside,
      Nat.zero_add]
  have slotOffset : ∀ i, i < preset.SLOTS_PER_EPOCH.toNat →
      (UInt64.ofNat (i + (epoch - 1) * preset.SLOTS_PER_EPOCH.toNat)).toNat %
        preset.SLOTS_PER_EPOCH.toNat = i := by
    intro i inside
    rw [slotNat i inside, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt inside]
  obtain ⟨chosen, chosenIff, chosenNodup, chosenEq⟩ : ∃ chosen : List Nat,
      (∀ i, i ∈ chosen ↔
        i < preset.SLOTS_PER_EPOCH.toNat ∧ quorum ≤ (paymentAt state gloas i).weight) ∧
      chosen.Nodup ∧
      releasedPayments (state.builderPendingPayments gloas).elements.toList
          preset.SLOTS_PER_EPOCH.toNat quorum =
        chosen.map fun i => (paymentAt state gloas i).withdrawal := by
    exact ⟨_, fun i => by simp, List.nodup_range.filter _,
      releasedPayments_eq_map state gloas quorum⟩
  -- A chosen position is that of a slot of the previous epoch, which leaves the window.
  have chosenPosition : ∀ i ∈ chosen, ∃ p, slotPaymentPosition state
      (UInt64.ofNat (i + (epoch - 1) * preset.SLOTS_PER_EPOCH.toNat)) = some p ∧ p.toNat = i := by
    intro i member
    obtain ⟨inside, reached⟩ := (chosenIff i).mp member
    have nonzero := (weighted i inside reached).1
    apply Option.map_eq_some_iff.mp
    rw [before, slotEpoch i inside, slotOffset i inside]
    split
    · omega
    · simp
  have chosenGone : ∀ i ∈ chosen, slotPaymentPosition moved
      (UInt64.ofNat (i + (epoch - 1) * preset.SLOTS_PER_EPOCH.toNat)) = none := by
    intro i member
    obtain ⟨inside, reached⟩ := (chosenIff i).mp member
    have nonzero := (weighted i inside reached).1
    apply Option.map_eq_none_iff.mp
    rw [afterPosition, slotEpoch i inside]
    split
    · omega
    · split
      · omega
      · rfl
  have closes : ∀ i ∈ chosen, PaymentOpen state gloas
      (UInt64.ofNat (i + (epoch - 1) * preset.SLOTS_PER_EPOCH.toNat)) ∧
      ¬ PaymentOpen moved gloas
        (UInt64.ofNat (i + (epoch - 1) * preset.SLOTS_PER_EPOCH.toNat)) := by
    intro i member
    obtain ⟨p, located, atIndex⟩ := chosenPosition i member
    obtain ⟨inside, reached⟩ := (chosenIff i).mp member
    refine ⟨Or.inl ⟨p, located, atIndex ▸ (weighted i inside reached).2⟩, ?_⟩
    rintro (⟨q, kept, -⟩ | ⟨atHeader, -, -, -⟩)
    · rw [chosenGone i member] at kept
      cases kept
    · rw [movedHeader] at atHeader
      rw [atHeader] at located
      rw [← atIndex, (fresh p located).1] at reached
      exact absurd (UInt64.lt_of_lt_of_le least reached) (by decide)
  -- A payment that the window holds after the step was one epoch later in the window before it.
  have shiftedWindow : ∀ slot n, slotPaymentPosition moved slot = some n →
      0 < (paymentAt moved gloas n.toNat).withdrawal.amount →
      ∃ p, slotPaymentPosition state slot = some p ∧
        paymentAt moved gloas n.toNat = paymentAt state gloas p.toNat := by
    intro slot n located amount
    have onNat : (slotPaymentPosition moved slot).map UInt64.toNat = some n.toNat := by
      rw [located]
      rfl
    rw [afterPosition] at onNat
    split at onNat
    · have later : n.toNat = preset.SLOTS_PER_EPOCH.toNat +
          slot.toNat % preset.SLOTS_PER_EPOCH.toNat := (Option.some.inj onNat).symm
      rw [beyond _ (by omega)] at amount
      exact absurd amount (by decide)
    · split at onNat
      · rename_i current
        have offset : n.toNat = slot.toNat % preset.SLOTS_PER_EPOCH.toNat :=
          (Option.some.inj onNat).symm
        have earlier : (slotPaymentPosition state slot).map UInt64.toNat =
            some (n.toNat + preset.SLOTS_PER_EPOCH.toNat) := by
          rw [before, ite_eq_left_of_eq_true _ _ (eq_true current), offset, Nat.add_comm]
        obtain ⟨p, source, shifted⟩ := Option.map_eq_some_iff.mp earlier
        refine ⟨p, source, ?_⟩
        rw [shifted]
        exact early _ (by rw [offset]; exact Nat.mod_lt _ one)
      · cases onNat
  refine ⟨quorum, chosen.map fun i => UInt64.ofNat (i + (epoch - 1) * preset.SLOTS_PER_EPOCH.toNat),
    found, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [List.Nodup, List.pairwise_map]
    refine chosenNodup.imp_of_mem fun {a b} memA memB differ same => differ ?_
    have := congrArg UInt64.toNat same
    rw [slotNat a ((chosenIff a).mp memA).1, slotNat b ((chosenIff b).mp memB).1] at this
    omega
  · rw [movedQueue, chosenEq, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i member
    obtain ⟨p, located, atIndex⟩ := chosenPosition i member
    obtain ⟨inside, reached⟩ := (chosenIff i).mp member
    simp only [Function.comp_apply, openWithdrawal, located, atIndex,
      (weighted i inside reached).2, ↓reduceIte]
  · intro slot member
    obtain ⟨i, picked, rfl⟩ := List.mem_map.mp member
    exact (closes i picked).1
  · intro slot member
    obtain ⟨i, picked, rfl⟩ := List.mem_map.mp member
    obtain ⟨inside, reached⟩ := (chosenIff i).mp picked
    have := step (weighted i inside reached).1
    rw [UInt64.lt_iff_toNat_lt, slotNat i inside]
    omega
  · rintro slot (⟨n, located, amount⟩ | ⟨atHeader, bidSlot, -, value⟩)
    · obtain ⟨p, source, same⟩ := shiftedWindow slot n located amount
      exact Or.inl (Or.inl ⟨p, source, same ▸ amount⟩)
    · rw [movedHeader] at atHeader
      rw [movedBid] at bidSlot value
      subst atHeader
      exact Or.inl (paymentOpen_latestBlock bidSlot value)
  · intro slot opened _
    by_cases window : PaymentInWindow moved gloas slot
    · obtain ⟨n, located, amount⟩ := window
      obtain ⟨p, source, same⟩ := shiftedWindow slot n located amount
      simp only [openWithdrawal, located, source, ← same, amount, ↓reduceIte]
    · rcases opened with inWindow | ⟨atHeader, -, -, -⟩
      · exact absurd inWindow window
      rw [movedHeader] at atHeader
      subst atHeader
      rw [openWithdrawal_eq_latestBidWithdrawal fresh rfl]
      have bidWithdrawal := latestBidWithdrawal_congr (congrFun movedBid gloas)
      unfold openWithdrawal
      cases located : slotPaymentPosition moved state.latestBlockHeader.slot with
      | none => exact bidWithdrawal
      | some n =>
        dsimp only
        rw [ite_eq_right_of_eq_false _ _ (eq_false fun amount => window ⟨n, located, amount⟩)]
        exact bidWithdrawal
  · rw [UInt64.le_iff_toNat_le, movedSlot]
    omega
  · intro slot member
    obtain ⟨i, picked, rfl⟩ := List.mem_map.mp member
    exact (closes i picked).2
  · intro slot p located inside reached
    have onNat : (slotPaymentPosition state slot).map UInt64.toNat = some p.toNat := by
      rw [located]
      rfl
    rw [before] at onNat
    split at onNat
    · have := Option.some.inj onNat
      omega
    · split at onNat
      · rename_i previous
        have offset : slot.toNat % preset.SLOTS_PER_EPOCH.toNat = p.toNat :=
          Option.some.inj onNat
        apply List.mem_map.mpr
        refine ⟨p.toNat, (chosenIff _).mpr ⟨inside, reached⟩, ?_⟩
        apply UInt64.toNat_inj.mp
        rw [slotNat _ inside, ← offset, ← previous]
        exact Nat.mod_add_div' _ _
      · cases onNat

end EthLib.Consensus
