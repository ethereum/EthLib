module

public import EthLib.Consensus.Proofs.Transition.ActiveKept
public import EthLib.Consensus.Proofs.Transition.PaymentReleaseBlock
public import EthLib.Consensus.Proofs.Transition.PaymentReleaseChain
public import EthLib.Consensus.Proofs.Transition.PaymentReleaseInvariants

/-!
# Proofs: runs of steps that pay the bid of a block

From Gloas the builder of a block pays its proposer through a pending payment.

A run of slots and blocks inside one fork, from Gloas on, releases each payment at most once.

A run across the upgrade to Heze is not covered.

A payment is paid here when its withdrawal joins the queue of the withdrawals of the builders.

[EIP-7732] adds the builders, their bids and their payments.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-! ## The facts on the payments -/

/-- From Gloas, the facts on the payments that the steps of a chain assume. -/
structure PaymentFacts (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) :
    Prop where
  -- The builder debt invariant holds, so the balance of each builder covers its debt.
  covered : BuilderDebtCovered state gloas
  -- A payment with weight has an amount.
  funded : WeightedPaymentsFunded state gloas
  -- In the genesis epoch, the first half of the window is empty.
  genesis : GenesisFirstHalfEmpty state gloas
  -- A latest bid with a value is at the slot of the latest block.
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
    -- A later step reopens only a payment at its own slot or later, so it cannot release it again.
    exact run.closed slot old (step.opened slot new)

/-! ## Chains -/

/-- Two releases between the same two states queue the same withdrawals.

So the withdrawals that a release queues are fixed by its two states. -/
theorem PaymentRelease.map_eq {gloas : .glamsterdam ≤ fork} {released other : List Slot}
    (one : PaymentRelease state after gloas released)
    (two : PaymentRelease state after gloas other) :
    released.map (openWithdrawal state gloas) = other.map (openWithdrawal state gloas) :=
  List.append_cancel_left (one.queue.symm.trans two.queue)

/-- From Gloas, slots and blocks inside one fork, one after another, from a first state.

A run carries the slots of the payments it releases, and the withdrawals it queues for them.

The withdrawals that each step queues are fixed by the states that the step computes.

Its payments are fixed too, up to their order. -/
inductive PaymentChain (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) :
    BeaconState preset fork → List Slot → List BuilderPendingWithdrawal → Prop
  /-- A state is a run of no step to itself. -/
  | refl : PaymentChain config checks state gloas state [] []
  /-- A run followed by one slot. -/
  | slot {second third : BeaconState preset fork} {released more : List Slot}
    {queued : List BuilderPendingWithdrawal} :
    PaymentChain config checks state gloas second released queued →
    -- A slot releases the payments of a release from the state before it to the state after it.
    advanceSlot config checks second = .ok third → PaymentRelease second third gloas more →
    -- Each of them reaches the quorum that the epoch transition computes after that slot.
    --
    -- So a slot lists only payments that reach the quorum.
    (∀ slot ∈ more, ReachesQuorum config checks second gloas slot) →
    -- Each released payment is closed after its step.
    (∀ slot ∈ more, ¬ PaymentOpen third gloas slot) →
    PaymentChain config checks state gloas third (released ++ more)
      (queued ++ more.map (openWithdrawal second gloas))
  /-- A run followed by one block. -/
  | block {second parented third : BeaconState preset fork} {released more : List Slot}
    {queued : List BuilderPendingWithdrawal} (engine : ExecutionEngine preset fork)
    (block : BeaconBlock preset fork) :
    PaymentChain config checks state gloas second released queued →
    Consensus.processBlock config checks engine second block = .ok third →
    Consensus.processParentExecutionPayload config checks second gloas block.body = .ok parented →
    -- A block releases those of a release up to the state that the payload of its parent computes.
    PaymentRelease second parented gloas more →
    -- It releases at most the payment of its parent, so a block lists only that payment.
    --
    -- The rest of the block releases nothing, and may pay out a prefix of the queue.
    more.Sublist [second.latestBlockHeader.slot] → PaymentStep parented third gloas [] →
    -- Each released payment is closed after its step.
    (∀ slot ∈ more, ¬ PaymentOpen third gloas slot) →
    PaymentChain config checks state gloas third (released ++ more)
      (queued ++ more.map (openWithdrawal second gloas))

/-- A run of slots and blocks is a run of payment steps, with the same lists. -/
theorem PaymentChain.paymentRun {gloas : .glamsterdam ≤ fork} {released : List Slot}
    {queued : List BuilderPendingWithdrawal}
    (chain : PaymentChain config checks state gloas after released queued) :
    PaymentRun state gloas after released queued := by
  induction chain with
  | refl => exact .refl
  | slot _ _ release _ closes ih => exact .step ih (.of_release release closes)
  | block _ _ _ _ _ release _ step closes ih =>
    exact .step ih (.of_release_trans release step closes)

/-- One step of a chain inside one fork never shrinks the builder registry. -/
theorem ChainStep.buildersGrow {gloas : .glamsterdam ≤ fork}
    {state after : BeaconState preset fork}
    (step : ChainStep config checks ⟨fork, state⟩ ⟨fork, after⟩) :
    (state.builders gloas).data.size ≤ (after.builders gloas).data.size := by
  rcases step.slot_or_block with computed | ⟨_, _, computed⟩
  · rw [advanceSlot_builders gloas computed]
    exact Nat.le_refl _
  · exact processBlock_buildersGrow gloas computed

/-- A run of steps of a chain inside one fork never shrinks the builder registry. -/
theorem buildersGrow_of_chainSteps {gloas : .glamsterdam ≤ fork}
    {first : BeaconState preset fork} {forked : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) ⟨fork, first⟩ forked) :
    ∀ {last : BeaconState preset fork}, forked = ⟨fork, last⟩ →
      (first.builders gloas).data.size ≤ (last.builders gloas).data.size := by
  induction steps with
  | refl =>
    intro last same
    cases same
    exact Nat.le_refl _
  | tail reach step more =>
    intro last same
    subst same
    obtain ⟨middle, rfl⟩ := fork_eq_of_chainSteps reach step
    exact Nat.le_trans (more rfl) step.buildersGrow

/-- From Gloas, chain steps inside one fork extend a run of slots and blocks that pay.

The facts on the payments must hold at the end of the run, and they then hold at the last state.

Each registry must hold at most 2^40 entries at the last state. -/
private theorem PaymentChain.extend (positive : preset.PaymentQuorumPositive)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) {gloas : .glamsterdam ≤ fork}
    {first start : BeaconState preset fork} {released : List Slot}
    {queued : List BuilderPendingWithdrawal}
    (chain : PaymentChain config checks first gloas start released queued)
    (holds : PaymentFacts start gloas) {forked : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) ⟨fork, start⟩ forked) :
    ∀ {last : BeaconState preset fork}, forked = ⟨fork, last⟩ →
      last.validators.data.size ≤ 2 ^ 40 → (last.builders gloas).data.size ≤ 2 ^ 40 →
      ∃ more extra, PaymentChain config checks first gloas last (released ++ more)
        (queued ++ extra) ∧ PaymentFacts last gloas := by
  induction steps with
  | refl =>
    intro last same _ _
    cases same
    exact ⟨[], [], by simpa only [List.append_nil] using chain, holds⟩
  | tail reach step more =>
    intro last same validatorsFit buildersFit
    subst same
    obtain ⟨middle, rfl⟩ := fork_eq_of_chainSteps reach step
    obtain ⟨added, extra, run, facts⟩ :=
      more rfl (Nat.le_trans step.registryGrows validatorsFit)
        (Nat.le_trans step.buildersGrow buildersFit)
    rcases step.slot_or_block with computed | ⟨engine, block, computed⟩
    · obtain ⟨released, release, closes, off, on⟩ := advanceSlot_release positive
        facts.covered.parentFresh facts.funded facts.genesis computed
      -- Off a boundary the slot releases nothing; at a boundary each release reaches the quorum.
      have reaches : ∀ slot ∈ released, ReachesQuorum config checks middle gloas slot := by
        intro slot member
        by_cases atBoundary : last.slot % preset.SLOTS_PER_EPOCH = 0
        · exact (on atBoundary slot).mp member
        · rw [off atBoundary] at member
          cases member
      exact ⟨_, _, by
        simpa only [List.append_assoc] using run.slot computed release reaches closes,
        facts.advanceSlot positive computed⟩
    · obtain ⟨_, _, parentOk, release, paid, closes, sub⟩ := processBlock_paymentRelease positive
        twoSlots facts.covered facts.bidAt validatorsFit buildersFit computed
      exact ⟨_, _, by
        simpa only [List.append_assoc] using run.block engine block computed parentOk release
          sub paid closes,
        facts.processBlock positive twoSlots validatorsFit buildersFit computed⟩

/-- A run of slots and blocks releases each payment at most once. -/
theorem PaymentChain.nodup {gloas : .glamsterdam ≤ fork} {released : List Slot}
    {queued : List BuilderPendingWithdrawal}
    (chain : PaymentChain config checks state gloas after released queued) : released.Nodup :=
  chain.paymentRun.nodup

/-- From Gloas, a run of chain steps inside one fork keeps the facts on the payments.

The preset needs a positive payment quorum and at least two slots in an epoch.

A run across the upgrade to Heze is not covered. -/
theorem PaymentFacts.chainSteps (positive : preset.PaymentQuorumPositive)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) {gloas : .glamsterdam ≤ fork}
    {first last : BeaconState preset fork}
    (steps : Relation.ReflTransGen (ChainStep config checks) ⟨fork, first⟩ ⟨fork, last⟩)
    -- The facts on the payments must hold at the first state.
    (holds : PaymentFacts first gloas)
    -- The registry of validators must hold at most 2^40 entries at the last state.
    (validatorsFit : last.validators.data.size ≤ 2 ^ 40)
    -- The registry of builders must hold at most 2^40 entries at the last state.
    (buildersFit : (last.builders gloas).data.size ≤ 2 ^ 40) : PaymentFacts last gloas := by
  obtain ⟨_, _, -, facts⟩ :=
    PaymentChain.extend positive twoSlots .refl holds steps rfl validatorsFit buildersFit
  exact facts

/-- From Gloas, a run of chain steps inside one fork is a run of slots and blocks that pay.

The preset needs a positive payment quorum and at least two slots in an epoch.

A run across the upgrade to Heze is not covered, since a run of payment steps stays in one fork. -/
theorem paymentChain_of_chainSteps (positive : preset.PaymentQuorumPositive)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) {gloas : .glamsterdam ≤ fork}
    {first last : BeaconState preset fork}
    (steps : Relation.ReflTransGen (ChainStep config checks) ⟨fork, first⟩ ⟨fork, last⟩)
    -- The facts on the payments must hold at the first state.
    (holds : PaymentFacts first gloas)
    -- The registry of validators must hold at most 2^40 entries at the last state.
    (validatorsFit : last.validators.data.size ≤ 2 ^ 40)
    -- The registry of builders must hold at most 2^40 entries at the last state.
    (buildersFit : (last.builders gloas).data.size ≤ 2 ^ 40) :
    ∃ released queued, PaymentChain config checks first gloas last released queued := by
  obtain ⟨_, _, chain, -⟩ :=
    PaymentChain.extend positive twoSlots .refl holds steps rfl validatorsFit buildersFit
  exact ⟨_, _, chain⟩

/-- From Gloas, along a chain through one slot that ends an epoch, that slot pays the quorum once.

The preset needs a positive payment quorum and at least two slots in an epoch.

The chain runs inside one fork, so a chain across the upgrade to Heze is not covered. -/
theorem chainSteps_paysQuorum (positive : preset.PaymentQuorumPositive)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) {gloas : .glamsterdam ≤ fork}
    {first middle next last : BeaconState preset fork}
    (before : Relation.ReflTransGen (ChainStep config checks) ⟨fork, first⟩ ⟨fork, middle⟩)
    (computed : advanceSlot config checks middle = .ok next)
    (behind : Relation.ReflTransGen (ChainStep config checks) ⟨fork, next⟩ ⟨fork, last⟩)
    -- The slot ends an epoch, with the facts on the payments holding at the first state.
    (boundary : next.slot % preset.SLOTS_PER_EPOCH = 0) (holds : PaymentFacts first gloas)
    -- The registry of validators must hold at most 2^40 entries at the last state.
    (validatorsFit : last.validators.data.size ≤ 2 ^ 40)
    -- The registry of builders must hold at most 2^40 entries at the last state.
    (buildersFit : (last.builders gloas).data.size ≤ 2 ^ 40) :
    -- It queues the withdrawals of exactly the previous epoch payments that reach its quorum.
    ∃ more : List Slot, (next.builderPendingWithdrawals gloas).data.toList =
        (middle.builderPendingWithdrawals gloas).data.toList ++
          more.map (openWithdrawal middle gloas) ∧
      -- That quorum is read on the state that the epoch transition reaches before its payment step.
      (∀ slot, slot ∈ more ↔ ReachesQuorum config checks middle gloas slot) ∧
      -- A run of slots and blocks from the first state to the last one releases each such payment.
      --
      -- That run releases no payment twice.
      ∃ released queued, PaymentChain config checks first gloas last released queued ∧
        released.Nodup ∧ ∀ slot ∈ more, slot ∈ released := by
  -- The registries at the state after the slot are at most those at the last state.
  have validators : next.validators.data.size ≤ last.validators.data.size :=
    registryGrows_of_chainSteps behind
  have builders := buildersGrow_of_chainSteps (gloas := gloas) behind rfl
  obtain ⟨_, _, chain, facts⟩ := PaymentChain.extend positive twoSlots .refl holds before rfl
    (Nat.le_trans (advanceSlot_kept computed).2.2 (Nat.le_trans validators validatorsFit))
    (by rw [← advanceSlot_builders gloas computed]; exact Nat.le_trans builders buildersFit)
  obtain ⟨more, release, closes, -, pays⟩ := advanceSlot_release positive
    facts.covered.parentFresh facts.funded facts.genesis computed
  have exactly := pays boundary
  obtain ⟨_, _, whole, -⟩ := PaymentChain.extend positive twoSlots
    (chain.slot computed release (fun slot member => (exactly slot).mp member) closes)
    (facts.advanceSlot positive computed) behind rfl validatorsFit buildersFit
  exact ⟨more, release.queue, exactly, _, _, whole, whole.nodup,
    fun slot member => List.mem_append_left _ (List.mem_append_right _ member)⟩

end EthLib.Consensus
