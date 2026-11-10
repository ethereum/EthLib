module

public import EthLib.Consensus.Proofs.Transition.PaymentReleaseInvariants
public import EthLib.Consensus.Proofs.Transition.PaymentReleaseWithdrawals

/-!
# Proofs: runs of steps that pay the bid of a block

From Gloas the builder of a block pays its proposer through a pending payment.

Each step of a chain queues the withdrawals of a list of open payments.

Those steps follow each other as a run, whose lists are the lists of its steps, in order.

A run releases each payment at most once.

A payment that a step releases is closed after it and older than its slot.

A later step reopens only a payment at its own slot or later, so it cannot release it again.

The steps assume a few facts on the payments.

The upgrade to Gloas starts with them, and the upgrade to Heze and each slot keep them.

A block keeps them under conditions on the preset and on the size of the registries.

[EIP-7732] adds the builders, their bids and their payments.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-! ## The facts on the payments -/

/-- From Gloas, the facts on the payments that the steps of a chain assume.

The builder debt invariant holds, so the balance of each builder covers its debt.

A payment with weight has an amount.

In the genesis epoch, the first half of the window is empty.

A latest bid with a value is at the slot of the latest block. -/
structure PaymentFacts (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) :
    Prop where
  covered : BuilderDebtCovered state gloas
  funded : WeightedPaymentsFunded state gloas
  genesis : GenesisFirstHalfEmpty state gloas
  bidAt : ValuedBidAtLatestBlock state gloas

/-- The upgrade to Gloas starts with the facts on the payments. -/
theorem paymentFacts_upgradeToGloas {pre : BeaconState preset .fusaka}
    {post : BeaconState preset .glamsterdam}
    (computed : upgradeToGloas config checks pre = .ok post) :
    PaymentFacts post (by decide) :=
  ⟨builderDebtCovered_upgradeToGloas computed, weightedPaymentsFunded_upgradeToGloas computed,
    genesisFirstHalfEmpty_upgradeToGloas computed, valuedBidAtLatestBlock_upgradeToGloas computed⟩

/-- The upgrade to Heze keeps the facts on the payments. -/
theorem PaymentFacts.upgradeToHeze {pre : BeaconState preset .glamsterdam}
    {post : BeaconState preset .hegota} (holds : PaymentFacts pre (by decide))
    (computed : upgradeToHeze config pre = .ok post) : PaymentFacts post (by decide) :=
  ⟨BuilderDebtCovered.upgradeToHeze holds.covered computed,
    WeightedPaymentsFunded.upgradeToHeze holds.funded computed,
    GenesisFirstHalfEmpty.upgradeToHeze holds.genesis computed,
    ValuedBidAtLatestBlock.upgradeToHeze holds.bidAt computed⟩

/-- From Gloas, with a positive quorum, one slot keeps the facts on the payments. -/
theorem PaymentFacts.advanceSlot (positive : preset.PaymentQuorumPositive)
    {gloas : .glamsterdam ≤ fork} (holds : PaymentFacts state gloas)
    (computed : advanceSlot config checks state = .ok after) : PaymentFacts after gloas :=
  ⟨BuilderDebtCovered.advanceSlot positive holds.covered computed,
    WeightedPaymentsFunded.advanceSlot holds.funded computed,
    GenesisFirstHalfEmpty.advanceSlot holds.genesis computed,
    ValuedBidAtLatestBlock.advanceSlot holds.bidAt computed⟩

/-- From Gloas, a block keeps the facts on the payments.

The preset needs a positive payment quorum and at least two slots in an epoch.

Each registry must hold at most 2^40 entries after the block. -/
theorem PaymentFacts.processBlock (positive : preset.PaymentQuorumPositive)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) {gloas : .glamsterdam ≤ fork}
    {block : BeaconBlock preset fork} (holds : PaymentFacts state gloas)
    (validatorsFit : after.validators.data.size ≤ 2 ^ 40)
    (buildersFit : (after.builders gloas).data.size ≤ 2 ^ 40)
    (computed : Consensus.processBlock config checks engine state block = .ok after) :
    PaymentFacts after gloas :=
  ⟨BuilderDebtCovered.processBlock positive twoSlots holds.covered validatorsFit buildersFit
      computed,
    WeightedPaymentsFunded.processBlock holds.funded computed,
    GenesisFirstHalfEmpty.processBlock holds.genesis computed,
    ValuedBidAtLatestBlock.processBlock gloas computed⟩

/-! ## Runs of steps -/

/-- Steps that queue the withdrawals of open payments, one after another, from a first state.

A run carries the slots of the payments it releases, and the withdrawals it queues for them.

Those lists are the lists of its steps, in order.

Each step queues the withdrawal of each payment it releases, as read on the state before it. -/
inductive PaymentRun (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) :
    BeaconState preset fork → List Slot → List BuilderPendingWithdrawal → Prop
  /-- A state is a run of no step to itself. -/
  | refl : PaymentRun state gloas state [] []
  /-- A run followed by one more step. -/
  | step {second third : BeaconState preset fork} {released more : List Slot}
    {queued : List BuilderPendingWithdrawal} :
    PaymentRun state gloas second released queued → PaymentStep second third gloas more →
    PaymentRun state gloas third (released ++ more)
      (queued ++ more.map (openWithdrawal second gloas))

/-- Two runs, one after the other, are a run. -/
theorem PaymentRun.append {gloas : .glamsterdam ≤ fork}
    {first second third : BeaconState preset fork} {released more : List Slot}
    {queued extra : List BuilderPendingWithdrawal}
    (one : PaymentRun first gloas second released queued)
    (two : PaymentRun second gloas third more extra) :
    PaymentRun first gloas third (released ++ more) (queued ++ extra) := by
  induction two with
  | refl => simpa using one
  | step _ step ih => simpa [← List.append_assoc] using .step ih step

/-- Dropping a prefix, appending, then dropping again is one drop from the appended list. -/
private theorem drop_append_drop {α : Type*} (items extra : List α) (first second : Nat) :
    (items.drop first ++ extra).drop second =
      (items ++ extra).drop (min first items.length + second) := by
  by_cases fits : first ≤ items.length
  · rw [Nat.min_eq_left fits, ← List.drop_drop, List.drop_append_of_le_length fits]
  · rw [Nat.min_eq_right (by omega), List.drop_of_length_le (show items.length ≤ first by omega),
      List.nil_append, List.drop_append]
    simp

/-- A run queues its withdrawals after the queue of its first state, and drops a prefix. -/
theorem PaymentRun.queue {gloas : .glamsterdam ≤ fork} {released : List Slot}
    {queued : List BuilderPendingWithdrawal} (run : PaymentRun state gloas after released queued) :
    ∃ count, (after.builderPendingWithdrawals gloas).data.toList =
      ((state.builderPendingWithdrawals gloas).data.toList ++ queued).drop count := by
  induction run with
  | refl => exact ⟨0, by simp⟩
  | step _ step ih =>
    obtain ⟨before, before_queue⟩ := ih
    obtain ⟨more, more_queue⟩ := step.queue
    exact ⟨min before _ + more, by
      rw [more_queue, before_queue, drop_append_drop, List.append_assoc]⟩

/-- Each payment that a run releases is closed after it, and older than its last slot. -/
private theorem PaymentRun.closed_past {gloas : .glamsterdam ≤ fork} {released : List Slot}
    {queued : List BuilderPendingWithdrawal} (run : PaymentRun state gloas after released queued) :
    ∀ slot ∈ released, ¬ PaymentOpen after gloas slot ∧ slot < after.slot := by
  induction run with
  | refl => simp
  | step _ step ih =>
    intro slot mem
    rcases List.mem_append.mp mem with old | new
    · obtain ⟨closed, past⟩ := ih slot old
      exact ⟨step.keepsClosed closed past, UInt64.lt_of_lt_of_le past step.forward⟩
    · exact ⟨step.closes slot new, UInt64.lt_of_lt_of_le (step.past slot new) step.forward⟩

/-- Each payment that a run releases is closed after it. -/
theorem PaymentRun.closed {gloas : .glamsterdam ≤ fork} {released : List Slot}
    {queued : List BuilderPendingWithdrawal} (run : PaymentRun state gloas after released queued) :
    ∀ slot ∈ released, ¬ PaymentOpen after gloas slot := by
  exact fun slot mem => (run.closed_past slot mem).1

/-- Each payment that a run releases is older than the slot of its last state. -/
theorem PaymentRun.past {gloas : .glamsterdam ≤ fork} {released : List Slot}
    {queued : List BuilderPendingWithdrawal} (run : PaymentRun state gloas after released queued) :
    ∀ slot ∈ released, slot < after.slot := by
  exact fun slot mem => (run.closed_past slot mem).2

/-- A run releases each payment at most once. -/
theorem PaymentRun.nodup {gloas : .glamsterdam ≤ fork} {released : List Slot}
    {queued : List BuilderPendingWithdrawal} (run : PaymentRun state gloas after released queued) :
    released.Nodup := by
  induction run with
  | refl => simp
  | step run step ih =>
    refine List.nodup_append.mpr ⟨ih, step.nodup, fun slot old slot' new same => ?_⟩
    subst same
    exact run.closed slot old (step.opened slot new)

end EthLib.Consensus
