module

public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Whistleblower

/-!
# Ownership of the consolidation payments

The tags, payments and ownership that follow each unit of balance through the consolidations.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety.Apriori.Internal

open Base Classical Cryptography.Bls Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable section

abbrev ix (x u : ForkedBeaconState preset) :=
  (getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat
theorem penalties_monotone (x : ForkedBeaconState preset) (high : Nat) :
    Monotone (windowPenalties (config := config) x high) := by
  intro a b less
  unfold windowPenalties
  have included : List.range a <+: List.range b := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le less
    rw [List.range_add]
    exact List.prefix_append _ _
  exact (included.sublist.map _).sum_le_sum (fun _ _ => Nat.zero_le _)

def commonSlashed (x y : ForkedBeaconState preset) (c : Finset BLSPubkey) :=
  Models.stake (effectiveWeight x.state) (c.filter (SlashedAt y.state ·))
def reducedDrift (x y : ForkedBeaconState preset) (c : Finset BLSPubkey) :=
  stateDriftOn (unslashedKeys x.state \ c) x y
def previousOnly (x : ForkedBeaconState preset) : Finset BLSPubkey :=
  keysAt x.state (getActiveValidatorIndices x.state (getPreviousEpoch x.state)) \ activeKeys x.state
def gainWithoutPreviousOnly (x y : ForkedBeaconState preset) : Nat :=
  ∑ k ∈ (recentKeys y.state \ previousOnly x), (effectiveWeight y.state k -
    Models.supported (unslashedKeys x.state) (effectiveWeight x.state) k)

def potential (x : ForkedBeaconState preset) (i : Nat) :=
  (x.state.validators.data[i]?.map fun v => max v.effectiveBalance.toNat
    (min (actualBalanceAt x i) (withdrawalMaxEffectiveBalance preset x.fork v).toNat)).getD 0

structure SelectedCharge where
  index : Nat
  amount : Nat
  epoch : Nat
  paidAt : Nat
inductive QueueTag where
  | initial (position : Nat)
  | fresh (callPosition : Nat)

/-- A tag of a source that joined the queue inside the window. -/
def QueueTag.isFresh : QueueTag → Bool
  | .initial _ => false
  | .fresh _ => true

attribute [simp] QueueTag.isFresh.eq_1 QueueTag.isFresh.eq_2

structure TaggedEntry where
  entry : PendingConsolidation
  tag : QueueTag
  amount : Nat
  epoch : Nat
def QueueErasure (queue : List TaggedEntry) (actual : List PendingConsolidation) : Prop :=
  queue.map (·.entry) = actual
structure Payment (preset : Preset) where
  source : Nat
  target : Nat
  amount : Nat
  epoch : Nat
  before : ForkedBeaconState preset
  after : ForkedBeaconState preset
def Paying (p : Payment preset) : Prop :=
  ∃ v, p.before.state.validators.data[p.source]? = some v ∧ v.slashed = false ∧
    v.withdrawableEpoch.toNat ≤ p.epoch ∧
    p.amount = min (actualBalanceAt p.before p.source) v.effectiveBalance.toNat ∧
    actualBalanceAt p.after p.source + p.amount = actualBalanceAt p.before p.source ∧
    actualBalanceAt p.after p.target = actualBalanceAt p.before p.target + p.amount
inductive PaymentPass {fork : Fork} (next : Epoch) :
    BeaconState preset fork → List PendingConsolidation →
    BeaconState preset fork → Nat → List (Payment preset) → Prop where
  | nil : PaymentPass next s [] s 0 []
  | waiting (found : getValidator s c.sourceIndex = .ok v) (unslashed : v.slashed = false)
      (later : next < v.withdrawableEpoch) : PaymentPass next s (c :: cs) s 0 []
  | slashed (found : getValidator s c.sourceIndex = .ok v) (slashed : v.slashed = true)
      (rest : PaymentPass next s cs t n payments) :
      PaymentPass next s (c :: cs) t (n + 1) payments
  | paid (found : getValidator s c.sourceIndex = .ok v) (unslashed : v.slashed = false)
      (due : v.withdrawableEpoch ≤ next) (balance : getBalance s c.sourceIndex = .ok b)
      (debited : decreaseBalance s c.sourceIndex (min b v.effectiveBalance) = .ok d)
      (credited : increaseBalance d c.targetIndex (min b v.effectiveBalance) = .ok u)
      (rest : PaymentPass next u cs t n payments) :
      PaymentPass next s (c :: cs) t (n + 1)
        (⟨c.sourceIndex.toNat, c.targetIndex.toNat, (min b v.effectiveBalance).toNat,
          next.toNat, ⟨fork, s⟩, ⟨fork, u⟩⟩ :: payments)
def EventPayments (e : BalanceEvent preset) (payments : List (Payment preset)) : Prop :=
  if e.source = .consolidations then
    ∃ fork, ∃ s t u : BeaconState preset fork, ∃ electra : .pectra ≤ fork,
      ∃ next n, e.before = ⟨fork, s⟩ ∧ e.after = ⟨fork, t⟩ ∧
      addChecked (getCurrentEpoch s) 1 = .ok next ∧
      processPendingConsolidations s electra = .ok t ∧
      PaymentPass next s (s.pendingConsolidations electra).data.toList u n payments ∧
      t.validators = u.validators ∧ t.balances = u.balances ∧
      (t.pendingConsolidations electra).data.toList =
        (s.pendingConsolidations electra).data.toList.drop n
  else payments = []
def SelectedPayments (selected : List SelectedCharge) (payments : List (Payment preset))
    (tags : List TaggedEntry) : Prop :=
  selected.length = payments.length ∧ payments.length = tags.length ∧
  ∀ i : Fin selected.length, ∃ p tag,
    payments[i.val]? = some p ∧ tags[i.val]? = some tag ∧ Paying p ∧
    (∃ n, tag.tag = .fresh n) ∧ tag.entry.sourceIndex.toNat = p.source ∧
    tag.entry.targetIndex.toNat = p.target ∧ selected[i].index = p.source ∧
    selected[i].amount = tag.amount ∧ selected[i].epoch = tag.epoch ∧
    selected[i].paidAt = p.epoch
def FreshTags (queue : List TaggedEntry) (calls : List (IndexedDepartureCall preset config)) :
    Prop :=
  (queue.map (·.tag)).Nodup ∧ ∀ e ∈ queue, ∀ n, e.tag = .fresh n →
    ∃ called, calls[n]? = some called ∧ called.index = some e.entry.sourceIndex.toNat ∧
      called.call.amount.toNat = e.amount ∧ called.call.epoch.toNat = e.epoch
def Cutoff (x : ForkedBeaconState preset) (high : Nat) (selected : List SelectedCharge) : Prop :=
  ∀ c ∈ selected, c.epoch + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤ c.paidAt ∧
    c.paidAt ≤ horizonEnd x high
def SelectedCapacity (x : ForkedBeaconState preset) (high : Nat)
    (selected : List SelectedCharge) : Prop :=
  (selected.map (·.amount)).sum ≤ dueConsolidationCarry (config := config) x high +
      consolidationTransfers (config := config) x high
structure OwnedRelease where
  baseline : Nat
  external : Nat
  sourceRound : Nat
def ReleasePartition (selected : List SelectedCharge) (payments : List (Payment preset))
    (allocations : List OwnedRelease) : Prop :=
  allocations.length = payments.length ∧ selected.length = payments.length ∧
  ∀ i : Fin payments.length, ∃ a c,
    allocations[i.val]? = some a ∧ selected[i.val]? = some c ∧
    payments[i].amount = a.baseline + a.external ∧ a.baseline ≤ c.amount + a.sourceRound
def ActualPaymentCoverage (events : List (BalanceEvent preset))
    (payments : List (Payment preset)) (initial : List PendingConsolidation) : Prop :=
  ∃ perEvent : Fin events.length → List (Payment preset),
    (∀ j, EventPayments events[j] (perEvent j)) ∧
    payments = ((List.finRange events.length).flatMap perEvent).filter fun p =>
      !initial.any (fun c => c.sourceIndex.toNat == p.source)

def initialTags (queue : List PendingConsolidation) : List TaggedEntry :=
  (queue.zipIdx).map fun (entry, position) => ⟨entry, .initial position, 0, 0⟩
def pendingQueue (s : ForkedBeaconState preset) : List PendingConsolidation :=
  if electra : .pectra ≤ s.fork then (s.state.pendingConsolidations electra).data.toList else []
inductive TaggedPass {fork : Fork} (next : Epoch) :
    BeaconState preset fork → List TaggedEntry → BeaconState preset fork →
    List TaggedEntry → List TaggedEntry → List (TaggedEntry × Payment preset) → Prop where
  | nil : TaggedPass next s [] s [] [] []
  | waiting (found : getValidator s tag.entry.sourceIndex = .ok v)
      (unslashed : v.slashed = false) (later : next < v.withdrawableEpoch) :
      TaggedPass next s (tag :: tags) s (tag :: tags) [] []
  | slashed (found : getValidator s tag.entry.sourceIndex = .ok v)
      (slashed : v.slashed = true) (rest : TaggedPass next s tags t suffix consumed payments) :
      TaggedPass next s (tag :: tags) t suffix (tag :: consumed) payments
  | paid (found : getValidator s tag.entry.sourceIndex = .ok v)
      (unslashed : v.slashed = false) (due : v.withdrawableEpoch ≤ next)
      (balance : getBalance s tag.entry.sourceIndex = .ok b)
      (debited : decreaseBalance s tag.entry.sourceIndex (min b v.effectiveBalance) = .ok d)
      (credited : increaseBalance d tag.entry.targetIndex (min b v.effectiveBalance) = .ok u)
      (rest : TaggedPass next u tags t suffix consumed payments) :
      TaggedPass next s (tag :: tags) t suffix (tag :: consumed)
        ((tag, ⟨tag.entry.sourceIndex.toNat, tag.entry.targetIndex.toNat,
          (min b v.effectiveBalance).toNat, next.toNat, ⟨fork, s⟩, ⟨fork, u⟩⟩) :: payments)
def TagEvent (e : BalanceEvent preset) (position : Nat)
    (before after consumed : List TaggedEntry) (payments : List (TaggedEntry × Payment preset))
    (calls : List (IndexedDepartureCall preset config)) : Prop :=
  QueueErasure before (pendingQueue e.before) ∧ QueueErasure after (pendingQueue e.after) ∧
  ((e.source ≠ .consolidations ∧ after = before ∧ consumed = [] ∧ payments = [] ∧ calls = []) ∨
    (∃ fork, ∃ s t : BeaconState preset fork, ∃ electra : .pectra ≤ fork,
      ∃ request sourceIndex source targetIndex called,
      e.source = .excess ∧ e.before = ⟨fork, s⟩ ∧ e.after = ⟨fork, t⟩ ∧
      processConsolidationRequest config s electra request = .ok t ∧
      getValidator s sourceIndex = .ok source ∧
      queueConsolidation config s electra sourceIndex source targetIndex = .ok t ∧
      called.index = some sourceIndex.toNat ∧ called.call.amount = source.effectiveBalance ∧
      called.call.earliest = s.earliestConsolidationEpoch electra ∧
      called.call.available = s.consolidationBalanceToConsume electra ∧
      called.call.epoch = t.earliestConsolidationEpoch electra ∧
      called.call.left = t.consolidationBalanceToConsume electra ∧
      computeActivationExitEpoch preset (getCurrentEpoch s) = .ok called.call.first ∧
      getConsolidationChurnLimit config s = .ok called.call.rate ∧
      after = before ++ [⟨⟨sourceIndex, targetIndex⟩, .fresh position,
        called.call.amount.toNat, called.call.epoch.toNat⟩] ∧
      consumed = [] ∧ payments = [] ∧ calls = [called]) ∨
    (∃ fork, ∃ s t u : BeaconState preset fork, ∃ electra : .pectra ≤ fork, ∃ next,
      e.source = .consolidations ∧ e.before = ⟨fork, s⟩ ∧ e.after = ⟨fork, t⟩ ∧
      addChecked (getCurrentEpoch s) 1 = .ok next ∧
      processPendingConsolidations s electra = .ok t ∧
      TaggedPass next s before u after consumed payments ∧
      t.validators = u.validators ∧ t.balances = u.balances ∧ calls = []))
inductive TagReplay : Nat → List (BalanceEvent preset) → List TaggedEntry →
    List TaggedEntry → List TaggedEntry → List (TaggedEntry × Payment preset) →
    List (IndexedDepartureCall preset config) → Prop where
  | nil : TagReplay position [] queue queue [] [] []
  | cons (one : TagEvent (config := config) e position before middle consumed paidPairs calls)
      (rest : TagReplay (position + calls.length) events middle after removed payments later) :
      TagReplay position (e :: events) before after (consumed ++ removed) (paidPairs ++ payments)
        (calls ++ later)
def FreshPaymentCoverage (events : List (BalanceEvent preset))
    (initial final consumed paidTags : List TaggedEntry) (payments : List (Payment preset))
    (calls : List (IndexedDepartureCall preset config)) : Prop :=
  ∃ allPaid : List (TaggedEntry × Payment preset),
    TagReplay (config := config) 0 events initial final consumed allPaid calls ∧
    let fresh := allPaid.filter fun pair => pair.1.tag.isFresh
    paidTags = fresh.map Prod.fst ∧ payments = fresh.map Prod.snd

inductive TokenOrigin where
  | initial (pot index unit : Nat)
  | credit (event index unit : Nat)
  | released (payment unit : Nat)
  deriving DecidableEq

/-- A unit of one of the four initial pots. -/
def TokenOrigin.isInitial : TokenOrigin → Bool
  | .initial _ _ _ => true
  | .credit _ _ _ => false
  | .released _ _ => false

attribute [simp] TokenOrigin.isInitial.eq_1 TokenOrigin.isInitial.eq_2 TokenOrigin.isInitial.eq_3

/-- A unit that a credit event issues. -/
def TokenOrigin.isCredit : TokenOrigin → Bool
  | .initial _ _ _ => false
  | .credit _ _ _ => true
  | .released _ _ => false

attribute [simp] TokenOrigin.isCredit.eq_1 TokenOrigin.isCredit.eq_2 TokenOrigin.isCredit.eq_3

/-- A unit that a released payment issues. -/
def TokenOrigin.isReleased : TokenOrigin → Bool
  | .initial _ _ _ => false
  | .credit _ _ _ => false
  | .released _ _ => true

attribute [simp] TokenOrigin.isReleased.eq_1 TokenOrigin.isReleased.eq_2 TokenOrigin.isReleased.eq_3

structure Ownership where
  issued : Finset TokenOrigin
  owner : TokenOrigin → Option Nat
  endpoint : Finset TokenOrigin
  original : Nat → Nat
  retired : Finset Nat
def held (o : Ownership) (i : Nat) : Finset TokenOrigin :=
  o.issued.filter fun token => o.owner token = some i
def OwnershipValid (o : Ownership) : Prop :=
  (∀ token, (o.owner token).isSome → token ∈ o.issued) ∧
    o.endpoint ⊆ o.issued ∧ ∀ token ∈ o.endpoint, (o.owner token).isSome
def OwnedTransfer (paymentPosition : Nat) (p : Payment preset) (allocation : OwnedRelease)
    (before after : Ownership) : Prop :=
  OwnershipValid before ∧ OwnershipValid after ∧
  ∃ moved minted : Finset TokenOrigin,
    moved ⊆ held before p.source ∧ moved.card = allocation.external ∧
    minted = (Finset.range allocation.baseline).image (TokenOrigin.released paymentPosition) ∧
    Disjoint before.issued minted ∧ after.issued = before.issued ∪ minted ∧
    p.amount = allocation.external + allocation.baseline ∧
    allocation.baseline ≤ before.original p.source ∧
    p.source ∉ before.retired ∧ after.retired = insert p.source before.retired ∧
    after.original p.source = 0 ∧
    (∀ i, i ≠ p.source → after.original i = before.original i) ∧
    (∀ token ∈ moved ∪ minted, after.owner token = some p.target) ∧
    (∀ token ∈ held before p.source, token ∉ moved → after.owner token = none) ∧
    (∀ token, token ∉ held before p.source → token ∉ minted →
      after.owner token = before.owner token) ∧
    after.endpoint = (before.endpoint \ held before p.source) ∪ moved ∪ minted
def OwnedCredit (eventPosition : Nat) (e : BalanceEvent preset)
    (before after : Ownership) : Prop :=
  OwnershipValid before ∧ OwnershipValid after ∧
  ∃ minted : Finset TokenOrigin,
    Disjoint before.issued minted ∧ after.issued = before.issued ∪ minted ∧
    (∀ token ∈ minted, ∃ i unit, token = .credit eventPosition i unit ∧
      unit < actualBalanceAt e.after i - actualBalanceAt e.before i ∧
      (e.source = .deposits →
        (e.before.state.validators.data[i]?.map (fun v =>
          decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch e.before.state).toNat))).getD
          false = false) ∧
      after.owner token = some i) ∧
    minted.card ≤ (if e.source = .deposits then funding_deposit_credit e
      else if e.source = .rewards ∨ e.source = .sync then e.creditLimit else otherCredit e) ∧
    (∀ token ∈ before.issued, after.owner token = before.owner token) ∧
    after.endpoint = before.endpoint ∪ minted ∧
    after.retired = before.retired ∧
    (∀ i, after.original i ≤ before.original i)
def OwnedFrame (before after : Ownership) : Prop :=
  OwnershipValid before ∧ OwnershipValid after ∧ after.issued = before.issued ∧
  (∀ token, after.owner token = before.owner token ∨ after.owner token = none) ∧
  after.endpoint ⊆ before.endpoint ∧ after.retired = before.retired ∧
    ∀ i, after.original i ≤ before.original i
inductive OwnedPayments : Nat → List (Payment preset) → List OwnedRelease →
    Ownership → Ownership → Prop where
  | nil : OwnedPayments position [] [] o o
  | cons (one : OwnedTransfer position p allocation before middle)
      (rest : OwnedPayments (position + 1) payments allocations middle after) :
      OwnedPayments position (p :: payments) (allocation :: allocations) before after
theorem OwnedTransfer.source_retirement
    (transfer : OwnedTransfer position p allocation before after) :
    p.source ∉ before.retired ∧ after.retired = insert p.source before.retired := by
  obtain ⟨_, _, moved, minted, _, _, _, _, _, _, _, fresh, retired, _⟩ := transfer
  exact ⟨fresh, retired⟩
private theorem OwnedPayments.source_once {payments : List (Payment preset)}
    (history : OwnedPayments position payments allocations before after) :
    (payments.map (·.source)).Nodup ∧
      ∀ p ∈ payments, p.source ∉ before.retired := by
  induction history with
  | nil => exact ⟨by simp, by simp⟩
  | @cons position p allocation before middle payments allocations after one _ ih =>
    obtain ⟨fresh, retired⟩ := one.source_retirement
    constructor
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih.1⟩
      intro member
      obtain ⟨later, inside, same⟩ := List.mem_map.mp member
      have absent := ih.2 later inside
      rw [retired, same] at absent
      exact absent (Finset.mem_insert_self _ _)
    · intro later member
      rcases List.mem_cons.mp member with rfl | inside
      · exact fresh
      · intro wasRetired
        exact ih.2 later inside (by rw [retired]; exact Finset.mem_insert_of_mem wasRetired)
/-- A transfer zeroes its source's original and keeps every other original. -/
theorem OwnedTransfer.original_le {position : Nat} {p : Payment preset}
    {allocation : OwnedRelease} {before after : Ownership}
    (transfer : OwnedTransfer position p allocation before after) :
    ∀ i, after.original i ≤ before.original i := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, source, others, _, _, _, _⟩ := transfer
  intro i
  by_cases same : i = p.source
  · rw [same, source]
    exact Nat.zero_le _
  · rw [others i same]

/-- Owned payments only retire keys and never raise an original.

Each transfer retires its source and keeps the earlier retired keys.

So every paid source ends retired.

Each transfer zeroes its source's original and keeps the others. -/
private theorem OwnedPayments.retired_original {payments : List (Payment preset)}
    (history : OwnedPayments position payments allocations before after) :
    (before.retired ⊆ after.retired ∧ ∀ p ∈ payments, p.source ∈ after.retired) ∧
      ∀ i, after.original i ≤ before.original i := by
  induction history with
  | nil => exact ⟨⟨Finset.Subset.refl _, by simp⟩, fun _ => Nat.le_refl _⟩
  | @cons position p allocation before middle payments allocations after one _ ih =>
    have retired := one.source_retirement.2
    refine ⟨⟨?_, ?_⟩, fun i => Nat.le_trans (ih.2 i) (one.original_le i)⟩
    · intro i member
      apply ih.1.1
      rw [retired]
      exact Finset.mem_insert_of_mem member
    · intro later member
      rcases List.mem_cons.mp member with rfl | inside
      · apply ih.1.1
        rw [retired]
        exact Finset.mem_insert_self _ _
      · exact ih.1.2 later inside

private theorem OwnedPayments.retired_mono {payments : List (Payment preset)}
    (history : OwnedPayments position payments allocations before after) :
    before.retired ⊆ after.retired ∧ ∀ p ∈ payments, p.source ∈ after.retired :=
  history.retired_original.1

/-- Owned payments never raise an original. -/
theorem OwnedPayments.original_le {payments : List (Payment preset)}
    (history : OwnedPayments position payments allocations before after) :
    ∀ i, after.original i ≤ before.original i :=
  history.retired_original.2

def OwnedEvent (eventPosition paymentPosition : Nat) (e : BalanceEvent preset)
    (tagged : List (TaggedEntry × Payment preset)) (allocations : List OwnedRelease)
    (before after : Ownership) : Prop :=
  if e.source = .consolidations then
    OwnedPayments paymentPosition (tagged.map Prod.snd) allocations before after ∧
      (∀ j : Fin tagged.length, ∃ a, allocations[j.val]? = some a ∧
        (match tagged[j].1.tag with | .initial _ => a.baseline = 0 | .fresh _ => True))
  else tagged = [] ∧ allocations = [] ∧
    (OwnedCredit eventPosition e before after ∨ OwnedFrame before after)
private theorem OwnedEvent.source_once
    {tagged : List (TaggedEntry × Payment preset)}
    (event : OwnedEvent eventPosition paymentPosition e tagged allocations before after) :
    (tagged.map (fun pair => pair.2.source)).Nodup ∧
      before.retired ⊆ after.retired ∧
      ∀ pair ∈ tagged, pair.2.source ∉ before.retired ∧ pair.2.source ∈ after.retired := by
  unfold OwnedEvent at event
  split at event
  · have once := event.1.source_once
    have mono := event.1.retired_mono
    refine ⟨?_, mono.1, ?_⟩
    · simpa only [List.map_map, Function.comp_def] using once.1
    · intro pair member
      have paid : pair.2 ∈ tagged.map Prod.snd := List.mem_map.mpr ⟨pair, member, rfl⟩
      exact ⟨once.2 pair.2 paid, mono.2 pair.2 paid⟩
  · obtain ⟨rfl, _, credit | frame⟩ := event
    · obtain ⟨_, _, minted, _, _, _, _, _, _, retired, _⟩ := credit
      exact ⟨by simp, retired ▸ Finset.Subset.refl _, by simp⟩
    · exact ⟨by simp, frame.2.2.2.2.2.1 ▸ Finset.Subset.refl _, by simp⟩
def initialPot (x : ForkedBeaconState preset) (high pot index : Nat) : Nat × Nat :=
  if pot = 0 then (index,
    if (x.state.validators.data[index]?).any
        (fun v => isActiveValidator v (getCurrentEpoch x.state))
    then potential x index - effectiveAt x index else 0)
  else if pot = 1 then (index,
    (x.state.validators.data[index]?.map fun v =>
      if !isActiveValidator v (getCurrentEpoch x.state) &&
          decide (getCurrentEpoch x.state < v.exitEpoch) then potential x index else 0).getD 0)
  else match (pendingQueue x)[index]? with
    | none => (0, 0)
    | some entry =>
      let i := entry.sourceIndex.toNat
      (i, (x.state.validators.data[i]?.map fun v =>
        if v.withdrawableEpoch.toNat ≤ horizonEnd x high then
          if pot = 2 then min (actualBalanceAt x i) v.effectiveBalance.toNat
          else if pot = 3 && !isActiveValidator v (getCurrentEpoch x.state) then
            min (actualBalanceAt x i) (withdrawalMaxEffectiveBalance preset x.fork v).toNat -
              v.effectiveBalance.toNat
          else 0
        else 0).getD 0)
def OwnedInitial (x : ForkedBeaconState preset) (high : Nat) (o : Ownership) : Prop :=
  OwnershipValid o ∧ o.retired = ∅ ∧
    o.issued.card ≤ initialCappedExcess x + preActiveStake x +
        dueConsolidationCredits x (driftHorizon x high) + pendingSourceExcess x high ∧
    (∀ token ∈ o.issued, ∃ pot index unit, token = .initial pot index unit ∧ pot < 4 ∧
      unit < (initialPot x high pot index).2 ∧
      o.owner token = some (initialPot x high pot index).1) ∧
    (∀ token ∈ o.endpoint, ∃ pot index unit, token = .initial pot index unit ∧ pot < 2) ∧
    (∀ i, o.original i = if (x.state.validators.data[i]?).any (fun v =>
      isActiveValidator v (getCurrentEpoch x.state) && !v.slashed &&
        v.exitEpoch == FAR_FUTURE_EPOCH) then effectiveAt x i else 0)
def NewReference (x : ForkedBeaconState preset) (i : Nat) : Prop :=
  (x.state.validators.data[i]?).any (fun v => isActiveValidator v (getCurrentEpoch x.state) &&
    !v.slashed && v.exitEpoch == FAR_FUTURE_EPOCH)
def InitialPending (x : ForkedBeaconState preset) (high i : Nat) : Prop :=
  ∃ c ∈ pendingQueue x, c.sourceIndex.toNat = i ∧
    (x.state.validators.data[i]?.map (·.withdrawableEpoch.toNat)).getD (horizonEnd x high + 1) ≤
        horizonEnd x high
def SupportedAt (epoch : Epoch) (v : Validator) : Prop :=
  v.slashed = false ∧
    (isActiveValidator v epoch ∨ isActiveValidator v (epoch - 1))
def FundingRelevant (u : ForkedBeaconState preset) (epoch : Epoch)
    (suffix : List PendingConsolidation) (i : Nat) : Prop :=
  ∃ v, u.state.validators.data[i]? = some v ∧
    (SupportedAt epoch v ∨ epoch < v.withdrawableEpoch ∨
      ∃ c ∈ suffix, c.sourceIndex.toNat = i)
def ReserveCut (x : ForkedBeaconState preset) (high : Nat)
    (u : ForkedBeaconState preset) (demandEpoch : Epoch)
    (suffix : List PendingConsolidation) (o : Ownership) : Prop :=
  OwnershipValid o ∧
    (∀ i ∈ o.retired, ∀ v, u.state.validators.data[i]? = some v →
      (∀ epoch, demandEpoch ≤ epoch → ¬ SupportedAt epoch v) ∧
        ¬ ∃ c ∈ suffix, c.sourceIndex.toNat = i) ∧
    (∀ i, o.original i ≤ effectiveAt x i ∧ (¬ NewReference x i → o.original i = 0)) ∧
    (∀ i, NewReference x i → i ∉ o.retired → FundingRelevant u demandEpoch suffix i →
      potential u i ≤ o.original i + (held o i).card) ∧
    (∀ i initial v, x.state.validators.data[i]? = some initial →
      isActiveValidator initial (getCurrentEpoch x.state) → initial.slashed = false →
      initial.exitEpoch ≠ FAR_FUTURE_EPOCH → u.state.validators.data[i]? = some v →
      (∃ epoch, demandEpoch ≤ epoch ∧ SupportedAt epoch v) →
      max (effectiveAt u i)
        (min (actualBalanceAt u i) (withdrawalMaxEffectiveBalance preset u.fork v).toNat) ≤
          effectiveAt x i + (held o i ∩ o.endpoint).card) ∧
    (∀ i, InitialPending x high i → i ∉ o.retired →
      FundingRelevant u demandEpoch suffix i → ∀ v,
      u.state.validators.data[i]? = some v →
      min (actualBalanceAt u i) (withdrawalMaxEffectiveBalance preset u.fork v).toNat ≤
        (held o i).card) ∧
    (∀ c ∈ suffix, ∀ v, u.state.validators.data[c.sourceIndex.toNat]? = some v →
      v.withdrawableEpoch ≤ demandEpoch → ¬ NewReference x c.sourceIndex.toNat →
      min (actualBalanceAt u c.sourceIndex.toNat)
        (withdrawalMaxEffectiveBalance preset u.fork v).toNat ≤
          (held o c.sourceIndex.toNat).card) ∧
    (∀ i v, u.state.validators.data[i]? = some v → ¬ NewReference x i →
      (¬ ∃ c ∈ pendingQueue x, c.sourceIndex.toNat = i) →
      (x.state.validators.data[i]?).all (fun initial =>
        !isActiveValidator initial (getCurrentEpoch x.state) &&
          !isActiveValidator initial (getPreviousEpoch x.state)) →
      (SupportedAt demandEpoch v ∨ demandEpoch < v.activationEpoch ∧ demandEpoch < v.exitEpoch ∨
        (∃ c ∈ suffix, c.sourceIndex.toNat = i) ∧
          (¬ ∃ c ∈ pendingQueue x, c.sourceIndex.toNat = i)) →
      max (effectiveAt u i)
        (min (actualBalanceAt u i) (withdrawalMaxEffectiveBalance preset u.fork v).toNat) ≤
          (held o i).card) ∧
    (∀ i, InitialPending x high i → ∀ v initial,
      u.state.validators.data[i]? = some v → x.state.validators.data[i]? = some initial →
      isActiveValidator initial (getCurrentEpoch x.state) → i ∉ o.retired →
      FundingRelevant u demandEpoch suffix i →
      min (actualBalanceAt u i) (withdrawalMaxEffectiveBalance preset u.fork v).toNat ≤
        effectiveAt x i + (held o i ∩ o.endpoint).card ∧
      effectiveAt u i ≤ effectiveAt x i + (held o i ∩ o.endpoint).card) ∧
    (∀ i v, u.state.validators.data[i]? = some v → SupportedAt demandEpoch v →
      v.pubkey ∉ previousOnly x →
      effectiveAt u i ≤ Models.supported (unslashedKeys x.state) (effectiveWeight x.state)
        v.pubkey + (held o i ∩ o.endpoint).card)
def AssignmentCut (rounding : Nat → Nat) (queue : List TaggedEntry) (o : Ownership) : Prop :=
  ∀ tag ∈ queue, ∀ position, tag.tag = .fresh position →
    o.original tag.entry.sourceIndex.toNat ≤ tag.amount + rounding tag.entry.sourceIndex.toNat
theorem assignmentCut_transport
    (cut : AssignmentCut rounding queue before)
    (decreasing : ∀ i, after.original i ≤ before.original i)
    (retained : suffix.Sublist queue) : AssignmentCut rounding suffix after := by
  intro tag member position fresh
  exact (decreasing _).trans (cut tag (retained.subset member) position fresh)
inductive ReservedPayments (x : ForkedBeaconState preset) (high : Nat) (rounding : Nat → Nat)
    {fork : Fork} (next : Epoch) : Nat → BeaconState preset fork → List TaggedEntry →
    BeaconState preset fork → List TaggedEntry → List (TaggedEntry × Payment preset) →
    List OwnedRelease → Ownership → Ownership → Prop where
  | nil (reserve : ReserveCut x high ⟨fork, s⟩ next [] o) :
      ReservedPayments x high rounding next position s [] s [] [] [] o o
  | waiting (found : getValidator s tag.entry.sourceIndex = .ok v)
      (unslashed : v.slashed = false) (later : next < v.withdrawableEpoch)
      (reserve : ReserveCut x high ⟨fork, s⟩ next ((tag :: tags).map (·.entry)) o)
      (assignment : AssignmentCut rounding (tag :: tags) o) :
      ReservedPayments x high rounding next position s (tag :: tags) s (tag :: tags) [] [] o o
  | slashed (found : getValidator s tag.entry.sourceIndex = .ok v)
      (slashed : v.slashed = true)
      (reserve : ReserveCut x high ⟨fork, s⟩ next ((tag :: tags).map (·.entry)) before)
      (assignment : AssignmentCut rounding (tag :: tags) before)
      (rest : ReservedPayments x high rounding next position s tags t suffix payments allocations
        before after) :
      ReservedPayments x high rounding next position s (tag :: tags) t suffix payments allocations
        before after
  | paid (found : getValidator s tag.entry.sourceIndex = .ok v)
      (unslashed : v.slashed = false) (due : v.withdrawableEpoch ≤ next)
      (balance : getBalance s tag.entry.sourceIndex = .ok b)
      (debited : decreaseBalance s tag.entry.sourceIndex (min b v.effectiveBalance) = .ok d)
      (credited : increaseBalance d tag.entry.targetIndex (min b v.effectiveBalance) = .ok u)
      (reserve : ReserveCut x high ⟨fork, s⟩ next ((tag :: tags).map (·.entry)) before)
      (assignment : AssignmentCut rounding (tag :: tags) before)
      (round : allocation.sourceRound = rounding tag.entry.sourceIndex.toNat)
      (moved : OwnedTransfer position
        ⟨tag.entry.sourceIndex.toNat, tag.entry.targetIndex.toNat,
          (min b v.effectiveBalance).toNat, next.toNat, ⟨fork, s⟩, ⟨fork, u⟩⟩
        allocation before middle)
      (initialNoRelease : match tag.tag with
        | .initial _ => allocation.baseline = 0
        | .fresh _ => allocation.baseline ≤ tag.amount + allocation.sourceRound ∧
            before.original tag.entry.sourceIndex.toNat ≤ tag.amount + allocation.sourceRound)
      (rest : ReservedPayments x high rounding next (position + 1) u tags t suffix payments
            allocations
        middle after) :
      ReservedPayments x high rounding next position s (tag :: tags) t suffix
        ((tag, ⟨tag.entry.sourceIndex.toNat, tag.entry.targetIndex.toNat,
          (min b v.effectiveBalance).toNat, next.toNat, ⟨fork, s⟩, ⟨fork, u⟩⟩) :: payments)
        (allocation :: allocations) before after
def ReservedEvent (x : ForkedBeaconState preset) (high eventPosition paymentPosition : Nat)
    (rounding : Nat → Nat)
    (e : BalanceEvent preset) (queue suffix : List TaggedEntry)
    (tagged : List (TaggedEntry × Payment preset)) (allocations : List OwnedRelease)
    (before after : Ownership) : Prop :=
  OwnedEvent eventPosition paymentPosition e tagged allocations before after ∧
    AssignmentCut rounding queue before ∧ AssignmentCut rounding suffix after ∧
    if e.source = .consolidations then
      ∃ fork, ∃ s t u : BeaconState preset fork, ∃ electra : .pectra ≤ fork, ∃ next,
        e.before = ⟨fork, s⟩ ∧ e.after = ⟨fork, t⟩ ∧
        addChecked (getCurrentEpoch s) 1 = .ok next ∧
        processPendingConsolidations s electra = .ok t ∧
        t.validators = u.validators ∧ t.balances = u.balances ∧
        ReservedPayments x high rounding next paymentPosition s queue u suffix tagged allocations
            before after
    else ReserveCut x high e.before (getCurrentEpoch e.before.state) (queue.map (·.entry)) before ∧
      ReserveCut x high e.after (getCurrentEpoch e.after.state) (suffix.map (·.entry)) after
inductive SilentStage : EpochStage → Prop where
  | justification : SilentStage .justification
  | inactivity : SilentStage .inactivity
  | registry : SilentStage .registry
  | eth1Reset : SilentStage .eth1Reset
  | payments : SilentStage .payments
  | effectiveBalances : SilentStage .effectiveBalances
  | slashingsReset : SilentStage .slashingsReset
  | randaoReset : SilentStage .randaoReset
  | history : SilentStage .history
  | participation : SilentStage .participation
  | syncCommittees : SilentStage .syncCommittees
  | proposerLookahead : SilentStage .proposerLookahead
  | ptcWindow : SilentStage .ptcWindow
inductive FrameStep (config : Config) (checks : SignatureChecks) :
    ForkedBeaconState preset → ForkedBeaconState preset → Prop where
  | cache {fork : Fork} {s t : BeaconState preset fork}
      (ok : processSlot s = .ok t) : FrameStep config checks ⟨fork, s⟩ ⟨fork, t⟩
  | epoch {fork : Fork} {s t : BeaconState preset fork}
      (silent : SilentStage stage) (ok : EpochStage.action config checks stage s = .ok t) :
      FrameStep config checks ⟨fork, s⟩ ⟨fork, t⟩
  | slot {fork : Fork} {s : BeaconState preset fork} (checked : addChecked s.slot 1 = .ok next) :
      FrameStep config checks ⟨fork, s⟩ ⟨fork, { s with slot := next }⟩
  | upgrade (ok : upgradeNext config checks s = .ok t)
      (silent : s.fork ≠ .dencun) : FrameStep config checks s t.val
  | header {fork : Fork} {s t : BeaconState preset fork} {block : BeaconBlock preset fork}
      (ok : processBlockHeader s block = .ok t) : FrameStep config checks ⟨fork, s⟩ ⟨fork, t⟩
  | randao {fork : Fork} {s t : BeaconState preset fork} {body : BeaconBlockBody preset fork}
      (ok : processRandao config checks s body = .ok t) :
      FrameStep config checks ⟨fork, s⟩ ⟨fork, t⟩
  | eth1 {fork : Fork} {s t : BeaconState preset fork} {body : BeaconBlockBody preset fork}
      (early : fork < .hegota) (ok : processEth1Data early s body = .ok t) :
      FrameStep config checks ⟨fork, s⟩ ⟨fork, t⟩
  | exit {fork : Fork} {s t : BeaconState preset fork} {exit : SignedVoluntaryExit}
      (ok : processVoluntaryExit config checks s exit = .ok t) :
      FrameStep config checks ⟨fork, s⟩ ⟨fork, t⟩
  | credentials {fork : Fork} {s t : BeaconState preset fork} {change : SignedBLSToExecutionChange}
      (ok : processBlsToExecutionChange config checks s change = .ok t) :
      FrameStep config checks ⟨fork, s⟩ ⟨fork, t⟩
  | depositRequest {fork : Fork} {s t : BeaconState preset fork} {request : DepositRequest}
      (electra : .pectra ≤ fork) (ok : processDepositRequest s electra request = .ok t) :
      FrameStep config checks ⟨fork, s⟩ ⟨fork, t⟩
  | withdrawalRequest {fork : Fork} {s t : BeaconState preset fork} {request : WithdrawalRequest}
      (electra : .pectra ≤ fork)
      (ok : processWithdrawalRequest config s electra request = .ok t) :
      FrameStep config checks ⟨fork, s⟩ ⟨fork, t⟩
inductive FramePath (config : Config) (checks : SignatureChecks) :
    ForkedBeaconState preset → ForkedBeaconState preset → Prop where
  | nil : FramePath config checks s s
  | cons (step : FrameStep config checks s u)
      (rest : FramePath config checks u t) : FramePath config checks s t
theorem FramePath.trans (one : FramePath config checks s u)
    (two : FramePath config checks u t) : FramePath config checks s t := by
  induction one with
  | nil => exact two
  | cons step _ ih => exact .cons step (ih two)
private theorem epochTrace_framePath {fork : Fork} {s t : BeaconState preset fork}
    (trace : EpochTrace (EpochStage.action config checks) stages s t)
    (silent : ∀ stage ∈ stages, SilentStage stage) :
    FramePath config checks ⟨fork, s⟩ ⟨fork, t⟩ := by
  induction trace with
  | nil => exact .nil
  | cons first rest ih =>
    exact .cons (.epoch (silent _ List.mem_cons_self) first)
      (ih (fun stage member => silent stage (List.mem_cons_of_mem _ member)))
private theorem epochSuffix_framePath {fork : Fork} {s t : BeaconState preset fork}
    (trace : EpochTrace (EpochStage.action config checks)
      (EpochStage.middleStages ++ EpochStage.tailStages) s t) :
    FramePath config checks ⟨fork, s⟩ ⟨fork, t⟩ := by
  apply epochTrace_framePath trace
  intro stage member
  simp only [EpochStage.middleStages, EpochStage.tailStages, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (h | h | h | h | h) | (h | h | h | h) <;> subst stage
  · exact .payments
  · exact .effectiveBalances
  · exact .slashingsReset
  · exact .randaoReset
  · exact .history
  · exact .participation
  · exact .syncCommittees
  · exact .proposerLookahead
  · exact .ptcWindow
theorem foldlM_framePath {α : Type} {fork : Fork}
    (action : BeaconState preset fork → α → Except TransitionError (BeaconState preset fork))
    (items : List α) {s t : BeaconState preset fork}
    (ok : items.foldlM action s = .ok t)
    (native : ∀ item ∈ items, ∀ a b, action a item = .ok b →
      FrameStep config checks ⟨fork, a⟩ ⟨fork, b⟩) :
    FramePath config checks ⟨fork, s⟩ ⟨fork, t⟩ :=
  foldlM_ok_invariant_of_mem (fun u => FramePath config checks ⟨fork, s⟩ ⟨fork, u⟩)
    (fun u item v member path computed => path.trans (.cons (native item member u v computed) .nil))
    .nil ok
theorem processEpoch_suffix_framePath {fork : Fork} {s t : BeaconState preset fork}
    (ok : processEpoch config checks s = .ok t) :
    ∃ middle, EpochTrace (EpochStage.action config checks) EpochStage.prefixStages s middle ∧
      FramePath config checks ⟨fork, middle⟩ ⟨fork, t⟩ := by
  have trace := processEpoch_trace ok
  change EpochTrace _ (EpochStage.prefixStages ++
    (EpochStage.middleStages ++ EpochStage.tailStages)) s t at trace
  obtain ⟨middle, headTrace, tailTrace⟩ := EpochTrace.append_iff.mp trace
  exact ⟨middle, headTrace, epochSuffix_framePath tailTrace⟩
def ReservedFrame (x : ForkedBeaconState preset) (high : Nat) (rounding : Nat → Nat)
    (u v : ForkedBeaconState preset) (fromEpoch toEpoch : Epoch)
    (queue : List TaggedEntry) (before after : Ownership) : Prop :=
  FramePath (config := config) (checks := checks) u v ∧
    fromEpoch ≤ toEpoch ∧ OwnedFrame before after ∧
    AssignmentCut rounding queue before ∧ AssignmentCut rounding queue after ∧
    QueueErasure queue (pendingQueue u) ∧ QueueErasure queue (pendingQueue v) ∧
    ReserveCut x high u fromEpoch (queue.map (·.entry)) before ∧
    ReserveCut x high v toEpoch (queue.map (·.entry)) after
theorem OwnedFrame.trans (one : OwnedFrame before middle)
    (two : OwnedFrame middle after) : OwnedFrame before after := by
  obtain ⟨validBefore, _, issuedOne, ownersOne, endpointOne, retiredOne, originalOne⟩ := one
  obtain ⟨_, validAfter, issuedTwo, ownersTwo, endpointTwo, retiredTwo, originalTwo⟩ := two
  refine ⟨validBefore, validAfter, issuedTwo.trans issuedOne, ?_,
    endpointTwo.trans endpointOne, retiredTwo.trans retiredOne, ?_⟩
  · intro token
    rcases ownersTwo token with same | erased
    · rcases ownersOne token with kept | erased
      · exact Or.inl (same.trans kept)
      · exact Or.inr (same.trans erased)
    · exact Or.inr erased
  · intro i
    exact (originalTwo i).trans (originalOne i)
theorem ReservedFrame.trans
    (one : ReservedFrame (config := config) (checks := checks) x high rounding
      u v fromEpoch middleEpoch queue before middle)
    (two : ReservedFrame (config := config) (checks := checks) x high rounding
      v w middleEpoch toEpoch queue middle after) :
    ReservedFrame (config := config) (checks := checks) x high rounding
      u w fromEpoch toEpoch queue before after := by
  obtain ⟨pathOne, epochOne, frameOne, assignmentBefore, _, erasureBefore, _,
    reserveBefore, _⟩ := one
  obtain ⟨pathTwo, epochTwo, frameTwo, _, assignmentAfter, _, erasureAfter, _,
    reserveAfter⟩ := two
  exact ⟨pathOne.trans pathTwo, UInt64.le_trans epochOne epochTwo, frameOne.trans frameTwo,
    assignmentBefore, assignmentAfter, erasureBefore, erasureAfter, reserveBefore, reserveAfter⟩
private theorem reserveCut_slot {fork : Fork} {s : BeaconState preset fork}
    (reserve : ReserveCut x high ⟨fork, s⟩ epoch suffix owned) :
    ReserveCut x high ⟨fork, { s with slot := next }⟩ epoch suffix owned := by
  simpa only [ReserveCut, potential, FundingRelevant, effectiveAt, actualBalanceAt, pendingQueue]
    using reserve
theorem reservedFrame_slot {fork : Fork} {s : BeaconState preset fork}
    (checked : addChecked s.slot 1 = .ok next)
    (reserve : ReserveCut x high ⟨fork, s⟩ epoch (queue.map (·.entry)) owned)
    (assignment : AssignmentCut rounding queue owned)
    (erasure : QueueErasure queue (pendingQueue ⟨fork, s⟩)) :
    ReservedFrame (config := config) (checks := checks) x high rounding
      ⟨fork, s⟩ ⟨fork, { s with slot := next }⟩ epoch epoch queue owned owned := by
  have identity : OwnedFrame owned owned :=
    ⟨reserve.1, reserve.1, rfl, fun _ => Or.inl rfl,
      Finset.Subset.refl _, rfl, fun _ => Nat.le_refl _⟩
  exact ⟨.cons (.slot checked) .nil, UInt64.le_refl _, identity, assignment, assignment,
    erasure, erasure, reserve, reserveCut_slot reserve⟩
private theorem reserveCut_cache {fork : Fork} {s t : BeaconState preset fork}
    (ok : processSlot s = .ok t)
    (reserve : ReserveCut x high ⟨fork, s⟩ epoch suffix owned) :
    ReserveCut x high ⟨fork, t⟩ epoch suffix owned := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok ok
  simpa only [ReserveCut, potential, FundingRelevant, effectiveAt, actualBalanceAt,
    getCurrentEpoch, pendingQueue] using reserve
private theorem reserveCut_justification {fork : Fork} {s t : BeaconState preset fork}
    (ok : processJustificationAndFinalization s = .ok t)
    (reserve : ReserveCut x high ⟨fork, s⟩ epoch suffix owned) :
    ReserveCut x high ⟨fork, t⟩ epoch suffix owned := by
  obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok ok
  · exact reserve
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    rw [← rest] at reserve
    simpa only [ReserveCut, potential, FundingRelevant, effectiveAt, actualBalanceAt,
      getCurrentEpoch, pendingQueue] using reserve
private theorem reserveCut_inactivity {fork : Fork} {s t : BeaconState preset fork}
    {altair : .altair ≤ fork} (ok : processInactivityUpdates config s altair = .ok t)
    (reserve : ReserveCut x high ⟨fork, s⟩ epoch suffix owned) :
    ReserveCut x high ⟨fork, t⟩ epoch suffix owned := by
  unfold processInactivityUpdates at ok
  split at ok
  · simp only [pure, Except.pure, Except.ok.injEq] at ok
    exact ok ▸ reserve
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, rfl⟩ := ok
    simpa only [ReserveCut, potential, FundingRelevant, effectiveAt, actualBalanceAt,
      getCurrentEpoch, pendingQueue] using reserve
theorem reservedFrame_cache {fork : Fork} {s t : BeaconState preset fork}
    (ok : processSlot s = .ok t)
    (reserve : ReserveCut x high ⟨fork, s⟩ epoch (queue.map (·.entry)) owned)
    (assignment : AssignmentCut rounding queue owned)
    (erasure : QueueErasure queue (pendingQueue ⟨fork, s⟩)) :
    ReservedFrame (config := config) (checks := checks) x high rounding
      ⟨fork, s⟩ ⟨fork, t⟩ epoch epoch queue owned owned := by
  have sameQueue : pendingQueue ⟨fork, t⟩ = pendingQueue ⟨fork, s⟩ := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok ok
    rfl
  have identity : OwnedFrame owned owned := by
    exact ⟨reserve.1, reserve.1, rfl, fun _ => Or.inl rfl,
      Finset.Subset.refl _, rfl, fun _ => Nat.le_refl _⟩
  exact ⟨.cons (.cache ok) .nil, UInt64.le_refl _, identity, assignment, assignment,
    erasure, sameQueue ▸ erasure, reserve, reserveCut_cache ok reserve⟩
private theorem reservedFrame_advanceSlot_nonlast {fork : Fork} {s t : BeaconState preset fork}
    (ok : advanceSlot config checks s = .ok t)
    (nonlast : ∀ next, addChecked s.slot 1 = .ok next →
      next % preset.SLOTS_PER_EPOCH ≠ 0)
    (reserve : ReserveCut x high ⟨fork, s⟩ epoch (queue.map (·.entry)) owned)
    (assignment : AssignmentCut rounding queue owned)
    (erasure : QueueErasure queue (pendingQueue ⟨fork, s⟩)) :
    ReservedFrame (config := config) (checks := checks) x high rounding
      ⟨fork, s⟩ ⟨fork, t⟩ epoch epoch queue owned owned := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨next, nextOk, cached, cacheOk, epoched, epochOk, rfl⟩ := ok
  have notLast := nonlast next nextOk
  simp only [epochIfLast, notLast, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at epochOk
  subst epoched
  have checked : addChecked cached.slot 1 = .ok next := by
    rw [processSlot_slot cacheOk]
    exact nextOk
  have first := reservedFrame_cache (config := config) (checks := checks)
    cacheOk reserve assignment erasure
  have last := reservedFrame_slot (config := config) (checks := checks)
    checked first.2.2.2.2.2.2.2.2 first.2.2.2.2.1 first.2.2.2.2.2.2.1
  exact first.trans last
theorem reservedFrame_advanceSlot_inside {fork : Fork} {s t : BeaconState preset fork}
    (ok : advanceSlot config checks s = .ok t)
    (nonlast : ∀ next, addChecked s.slot 1 = .ok next →
      next % preset.SLOTS_PER_EPOCH ≠ 0)
    (reserve : ReserveCut x high ⟨fork, s⟩ (getCurrentEpoch s) (queue.map (·.entry)) owned)
    (assignment : AssignmentCut rounding queue owned)
    (erasure : QueueErasure queue (pendingQueue ⟨fork, s⟩)) :
    ReservedFrame (config := config) (checks := checks) x high rounding
      ⟨fork, s⟩ ⟨fork, t⟩ (getCurrentEpoch s) (getCurrentEpoch t) queue owned owned := by
  have sameEpoch : getCurrentEpoch t = getCurrentEpoch s := by
    obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
    have checked : addChecked s.slot 1 = .ok next :=
      addChecked_ok_iff.mpr ⟨by
        change s.slot.toNat + 1 < 2 ^ 64
        have small := next.toNat_lt
        omega, sum⟩
    have notLast := nonlast next checked
    simp only [epochIfLast, notLast, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epoched
    apply UInt64.toNat_inj.mp
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
    exact nextSlot_epoch_of_inside sum notLast
  rw [sameEpoch]
  exact reservedFrame_advanceSlot_nonlast ok nonlast reserve assignment erasure
theorem reservedFrame_justification {fork : Fork} {s t : BeaconState preset fork}
    (ok : processJustificationAndFinalization s = .ok t)
    (reserve : ReserveCut x high ⟨fork, s⟩ epoch (queue.map (·.entry)) owned)
    (assignment : AssignmentCut rounding queue owned)
    (erasure : QueueErasure queue (pendingQueue ⟨fork, s⟩)) :
    ReservedFrame (config := config) (checks := checks) x high rounding
      ⟨fork, s⟩ ⟨fork, t⟩ epoch epoch queue owned owned := by
  have sameQueue : pendingQueue ⟨fork, t⟩ = pendingQueue ⟨fork, s⟩ := by
    obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok ok
    · rfl
    · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
      rw [← rest]
      rfl
  have identity : OwnedFrame owned owned :=
    ⟨reserve.1, reserve.1, rfl, fun _ => Or.inl rfl,
      Finset.Subset.refl _, rfl, fun _ => Nat.le_refl _⟩
  exact ⟨.cons (.epoch .justification ok) .nil, UInt64.le_refl _, identity,
    assignment, assignment, erasure, sameQueue ▸ erasure, reserve,
    reserveCut_justification ok reserve⟩
theorem reservedFrame_inactivity {fork : Fork} {s t : BeaconState preset fork}
    (ok : EpochStage.action config checks .inactivity s = .ok t)
    (reserve : ReserveCut x high ⟨fork, s⟩ epoch (queue.map (·.entry)) owned)
    (assignment : AssignmentCut rounding queue owned)
    (erasure : QueueErasure queue (pendingQueue ⟨fork, s⟩)) :
    ReservedFrame (config := config) (checks := checks) x high rounding
      ⟨fork, s⟩ ⟨fork, t⟩ epoch epoch queue owned owned := by
  have transport : ReserveCut x high ⟨fork, t⟩ epoch (queue.map (·.entry)) owned ∧
      pendingQueue ⟨fork, t⟩ = pendingQueue ⟨fork, s⟩ := by
    simp only [EpochStage.action] at ok
    split at ok
    · constructor
      · exact reserveCut_inactivity ok reserve
      · unfold processInactivityUpdates at ok
        split at ok
        · simp only [pure, Except.pure, Except.ok.injEq] at ok
          subst t
          rfl
        · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
          obtain ⟨_, _, _, _, rfl⟩ := ok
          rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      subst t
      exact ⟨reserve, rfl⟩
  have identity : OwnedFrame owned owned :=
    ⟨reserve.1, reserve.1, rfl, fun _ => Or.inl rfl,
      Finset.Subset.refl _, rfl, fun _ => Nat.le_refl _⟩
  exact ⟨.cons (.epoch .inactivity ok) .nil, UInt64.le_refl _, identity,
    assignment, assignment, erasure, transport.2 ▸ erasure, reserve, transport.1⟩
def eventDemandEpoch (e : BalanceEvent preset) : Epoch :=
  if e.source = .consolidations then getCurrentEpoch e.before.state + 1
  else getCurrentEpoch e.after.state
inductive ReservedReplay (x : ForkedBeaconState preset) (high : Nat) (rounding : Nat → Nat) :
    ForkedBeaconState preset → Epoch → ForkedBeaconState preset → Epoch →
    Nat → Nat → Nat → List (BalanceEvent preset) → List TaggedEntry → List TaggedEntry →
    List (TaggedEntry × Payment preset) → List OwnedRelease →
    List (IndexedDepartureCall preset config) → Ownership → Ownership → Prop where
  | nil (frame : ReservedFrame (config := config) (checks := checks)
        x high rounding start finish startEpoch finishEpoch queue before after) :
      ReservedReplay x high rounding start startEpoch finish finishEpoch
        eventPosition paymentPosition callPosition [] queue queue [] [] [] before after
  | cons (frame : ReservedFrame (config := config) (checks := checks) x high rounding start e.before
        startEpoch
        (getCurrentEpoch e.before.state) queue before eventOwned)
      (taggedEvent : TagEvent (config := config) e callPosition queue middle consumed tagged calls)
      (ownedEvent : ReservedEvent x high eventPosition paymentPosition rounding e queue middle
        tagged allocations eventOwned midOwned)
      (rest : ReservedReplay x high rounding e.after (eventDemandEpoch e) finish finishEpoch
        (eventPosition + 1) (paymentPosition + tagged.length)
        (callPosition + calls.length) events middle final payments restAllocations restCalls
        midOwned after) :
      ReservedReplay x high rounding start startEpoch finish finishEpoch
        eventPosition paymentPosition callPosition (e :: events) queue final
        (tagged ++ payments) (allocations ++ restAllocations) (calls ++ restCalls) before after
theorem ReservedPayments.paired_rounds
    {tagged : List (TaggedEntry × Payment preset)}
    (history : ReservedPayments x high rounding next position s queue t
      suffix tagged allocations before after) :
    List.Forall₂ (fun pair allocation => allocation.sourceRound = rounding pair.2.source)
      tagged allocations := by
  induction history with
  | nil => exact .nil
  | waiting => exact .nil
  | slashed _ _ _ _ _ ih => exact ih
  | paid _ _ _ _ _ _ _ _ round _ _ _ ih => exact .cons round ih
theorem ReservedEvent.paired_rounds
    {tagged : List (TaggedEntry × Payment preset)}
    (event : ReservedEvent x high eventPosition paymentPosition rounding e
      queue suffix tagged allocations before after) :
    List.Forall₂ (fun pair allocation => allocation.sourceRound = rounding pair.2.source)
      tagged allocations := by
  by_cases consolidation : e.source = .consolidations
  · have pass := event.2.2.2
    simp only [consolidation, ↓reduceIte] at pass
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, pass⟩ := pass
    exact pass.paired_rounds
  · have empty := event.1
    unfold OwnedEvent at empty
    simp only [consolidation, ↓reduceIte] at empty
    rw [empty.1, empty.2.1]
    exact .nil
theorem ReservedReplay.paired_rounds
    {tagged : List (TaggedEntry × Payment preset)}
    (history : ReservedReplay (config := config) (checks := checks) x high rounding
      start startEpoch finish finishEpoch eventPosition paymentPosition callPosition
      events queue final tagged allocations calls before after) :
    List.Forall₂ (fun pair allocation => allocation.sourceRound = rounding pair.2.source)
      tagged allocations := by
  induction history with
  | nil => exact .nil
  | cons _ _ event _ ih => exact List.rel_append event.paired_rounds ih
theorem ReservedPayments.paired_releases
    {tagged : List (TaggedEntry × Payment preset)}
    (history : ReservedPayments x high rounding next position s queue t
      suffix tagged allocations before after) :
    List.Forall₂ (fun pair allocation => (match pair.1.tag with
      | .initial _ => allocation.baseline = 0
      | .fresh _ => allocation.baseline ≤ pair.1.amount + allocation.sourceRound) ∧
        pair.2.amount = allocation.external + allocation.baseline)
      tagged allocations := by
  induction history with
  | nil => exact .nil
  | waiting => exact .nil
  | slashed _ _ _ _ _ ih => exact ih
  | paid _ _ _ _ _ _ _ _ _ moved baseline _ ih =>
    refine .cons ⟨?_, moved.2.2.choose_spec.choose_spec.2.2.2.2.2.1⟩ ih
    split <;> simp_all
theorem ReservedEvent.paired_releases
    {tagged : List (TaggedEntry × Payment preset)}
    (event : ReservedEvent x high eventPosition paymentPosition rounding e
      queue suffix tagged allocations before after) :
    List.Forall₂ (fun pair allocation => (match pair.1.tag with
      | .initial _ => allocation.baseline = 0
      | .fresh _ => allocation.baseline ≤ pair.1.amount + allocation.sourceRound) ∧
        pair.2.amount = allocation.external + allocation.baseline)
      tagged allocations := by
  by_cases consolidation : e.source = .consolidations
  · have pass := event.2.2.2
    simp only [consolidation, ↓reduceIte] at pass
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, pass⟩ := pass
    exact pass.paired_releases
  · have empty := event.1
    unfold OwnedEvent at empty
    simp only [consolidation, ↓reduceIte] at empty
    rw [empty.1, empty.2.1]
    exact .nil
theorem ReservedReplay.paired_releases
    {tagged : List (TaggedEntry × Payment preset)}
    (history : ReservedReplay (config := config) (checks := checks) x high rounding
      start startEpoch finish finishEpoch eventPosition paymentPosition callPosition
      events queue final tagged allocations calls before after) :
    List.Forall₂ (fun pair allocation => (match pair.1.tag with
      | .initial _ => allocation.baseline = 0
      | .fresh _ => allocation.baseline ≤ pair.1.amount + allocation.sourceRound) ∧
        pair.2.amount = allocation.external + allocation.baseline)
      tagged allocations := by
  induction history with
  | nil => exact .nil
  | cons _ _ event _ ih => exact List.rel_append event.paired_releases ih
theorem ReservedReplay.paired_baselines
    {tagged : List (TaggedEntry × Payment preset)}
    (history : ReservedReplay (config := config) (checks := checks) x high rounding
      start startEpoch finish finishEpoch eventPosition paymentPosition callPosition
      events queue final tagged allocations calls before after) :
    List.Forall₂ (fun pair allocation => match pair.1.tag with
      | .initial _ => allocation.baseline = 0
      | .fresh _ => allocation.baseline ≤ pair.1.amount + allocation.sourceRound)
      tagged allocations :=
  history.paired_releases.imp fun _ _ both => both.1
private theorem ReservedReplay.source_once
    {tagged : List (TaggedEntry × Payment preset)}
    (history : ReservedReplay (config := config) (checks := checks) x high rounding
      start startEpoch finish finishEpoch eventPosition paymentPosition callPosition
      events queue final tagged allocations calls before after) :
    (tagged.map (fun pair => pair.2.source)).Nodup ∧
      before.retired ⊆ after.retired ∧
      ∀ pair ∈ tagged, pair.2.source ∉ before.retired ∧ pair.2.source ∈ after.retired := by
  induction history with
  | nil frame =>
    have retired := frame.2.2.1.2.2.2.2.2.1
    exact ⟨by simp, retired ▸ Finset.Subset.refl _, by simp⟩
  | cons frame _ ownedEvent _ ih =>
    have retired := frame.2.2.1.2.2.2.2.2.1
    have first := ownedEvent.1.source_once
    rw [retired] at first
    refine ⟨?_, first.2.1.trans ih.2.1, ?_⟩
    · simp only [List.map_append, List.nodup_append]
      refine ⟨first.1, ih.1, ?_⟩
      intro source headMember target tailMember same
      obtain ⟨head, headInside, headEq⟩ := List.mem_map.mp headMember
      obtain ⟨later, laterInside, laterEq⟩ := List.mem_map.mp tailMember
      have retiredHead := (first.2.2 head headInside).2
      have fresh := (ih.2.2 later laterInside).1
      rw [headEq] at retiredHead
      rw [laterEq, ← same] at fresh
      exact fresh retiredHead
    · intro pair member
      rcases List.mem_append.mp member with head | later
      · exact ⟨(first.2.2 pair head).1, ih.2.1 (first.2.2 pair head).2⟩
      · exact ⟨fun old => (ih.2.2 pair later).1 (first.2.1 old), (ih.2.2 pair later).2⟩
private theorem source_round_sum_le (sources : List Nat) (carrier : Finset Nat) (increment : Nat)
    (unique : sources.Nodup) :
    (sources.map fun i => if i ∈ carrier then increment else 0).sum ≤ increment * carrier.card := by
  have exactSum : (sources.map fun i => if i ∈ carrier then increment else 0).sum =
      increment * (sources.filter (fun i => decide (i ∈ carrier))).length := by
    clear unique
    induction sources with
    | nil => simp
    | cons i rest ih =>
      by_cases inside : i ∈ carrier <;> simp [inside, ih, Nat.mul_add, Nat.add_comm]
  rw [exactSum]
  have sub : (sources.filter (fun i => decide (i ∈ carrier))).toFinset ⊆ carrier := by
    intro i member
    exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp member)).2
  have count := Finset.card_le_card sub
  rw [List.toFinset_card_of_nodup (unique.filter _)] at count
  exact Nat.mul_le_mul_left increment count
private theorem zip_fst_sublist {α β : Type} (left : List α) (right : List β) :
    ((left.zip right).map Prod.fst).Sublist left := by
  induction left generalizing right with
  | nil => simp
  | cons a left ih =>
    cases right with
    | nil => simp
    | cons b right => exact (ih right).cons_cons a
private theorem ReservedReplay.selected_allocation_round_sum_le
    {tagged : List (TaggedEntry × Payment preset)}
    (history : ReservedReplay (config := config) (checks := checks) x high rounding
      start startEpoch finish finishEpoch eventPosition paymentPosition callPosition
      events queue final tagged allocations calls before after)
    (select : (TaggedEntry × Payment preset) × OwnedRelease → Bool)
    (carrier : Finset Nat) (increment : Nat)
    (rounds : ∀ pair ∈ (tagged.zip allocations).filter select,
      pair.2.sourceRound = if pair.1.2.source ∈ carrier then increment else 0) :
    (((tagged.zip allocations).filter select).map fun pair => pair.2.sourceRound).sum ≤
      increment * carrier.card := by
  have selectedSub : (((tagged.zip allocations).filter select).map Prod.fst).Sublist tagged :=
    (List.filter_sublist.map _).trans (zip_fst_sublist tagged allocations)
  have unique := history.source_once.1.sublist (selectedSub.map (fun pair => pair.2.source))
  have count := source_round_sum_le _ carrier increment unique
  simp only [List.map_map, Function.comp_def] at count
  have same := List.map_congr_left rounds
  rw [same]
  exact count
theorem ReservedReplay.selected_round_sum_le
    {tagged : List (TaggedEntry × Payment preset)}
    (carrier : Finset Nat) (increment : Nat)
    (history : ReservedReplay (config := config) (checks := checks) x high
      (fun i => if i ∈ carrier then increment else 0)
      start startEpoch finish finishEpoch eventPosition paymentPosition callPosition
      events queue final tagged allocations calls before after)
    (select : (TaggedEntry × Payment preset) × OwnedRelease → Bool) :
    tagged.length = allocations.length ∧
      (((tagged.zip allocations).filter select).map fun pair => pair.2.sourceRound).sum ≤
        increment * carrier.card := by
  refine ⟨history.paired_rounds.length_eq,
    history.selected_allocation_round_sum_le select carrier increment ?_⟩
  intro pair member
  exact List.forall₂_zip history.paired_rounds (List.mem_filter.mp member).1
def EndpointDemand (x y : ForkedBeaconState preset) (o : Ownership) : Prop :=
  ∀ k ∈ recentKeys y.state \ previousOnly x,
    ∃ i, y.state.validators.data[i]?.any (fun v => v.pubkey == k) ∧
      effectiveWeight y.state k - Models.supported (unslashedKeys x.state)
        (effectiveWeight x.state) k ≤ (held o i ∩ o.endpoint).card
def CumulativeFunding (x y : ForkedBeaconState preset) (high : Nat)
    (events : List (BalanceEvent preset)) (selected : List SelectedCharge)
    (allocations : List OwnedRelease) (before after : Ownership) : Prop :=
  let initial := after.issued.filter (·.isInitial)
  let credits := after.issued.filter (·.isCredit)
  let releases := after.issued.filter (·.isReleased)
  initial = before.issued ∧
    credits.card ≤ (events.map funding_deposit_credit).sum +
      sourceCredits .rewards events + sourceCredits .sync events + (events.map otherCredit).sum ∧
    releases.card = (allocations.map (·.baseline)).sum ∧
    (events.map funding_deposit_credit).sum + fundingCarry y ≤
      fundingCarry x +
          ((List.range (driftHorizon x high + 1)).map (exitFlowAt (config := config) x high)).sum ∧
    sourceCredits .rewards events + sourceCredits .sync events ≤
        windowIssuance (config := config) x high ∧
    (events.map otherCredit).sum ≤ whistleblowerAllowanceAt (config := config) x high ∧
    (selected.map (·.amount)).sum ≤ dueConsolidationCarry (config := config) x high +
        consolidationTransfers (config := config) x high ∧
    releases.card ≤ (selected.map (·.amount)).sum + roundingBudget (config := config) x high ∧
    after.issued.card = initial.card + credits.card + releases.card
theorem cumulativeFunding_bound
    (electra : .pectra ≤ x.fork) (initial : OwnedInitial x high before)
    (funding : CumulativeFunding (config := config) x y high events selected allocations before
          after) :
    after.issued.card ≤ gainBudget (config := config) x high := by
  obtain ⟨same, credit, _released, deposits, rewards, other, charges, release, total⟩ := funding
  have start := initial.2.2.1
  unfold gainBudget activationBudget creditBudget
  simp only [ite_eq_left electra]
  have noCrossing : preElectraEpochs config x high = 0 := by
    have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
    simp only [preElectraEpochs, notBefore, ↓reduceIte]
  simp only [noCrossing, Nat.lt_irrefl, ↓reduceIte, Nat.add_zero]
  rw [same] at total
  omega
def TerminalAllocation (x y : ForkedBeaconState preset) (o : Ownership)
    (tokens : BLSPubkey → Finset TokenOrigin) : Prop :=
    (∀ k ∈ recentKeys y.state \ previousOnly x,
      tokens k ⊆ o.endpoint ∧
      ∃ i, y.state.validators.data[i]?.any (fun v => v.pubkey == k) ∧
        tokens k ⊆ held o i ∧
        (tokens k).card = effectiveWeight y.state k -
          Models.supported (unslashedKeys x.state) (effectiveWeight x.state) k) ∧
    (∀ k ∈ recentKeys y.state \ previousOnly x,
      ∀ l ∈ recentKeys y.state \ previousOnly x, k ≠ l → Disjoint (tokens k) (tokens l)) ∧
    (∑ k ∈ (recentKeys y.state \ previousOnly x) ∩ unslashedKeys x.state,
      (tokens k).card) +
      (∑ k ∈ (recentKeys y.state \ previousOnly x) \ unslashedKeys x.state,
        (tokens k).card) ≤ o.issued.card
theorem new_reference_loss_boundary_le
    (U supported boundary departed : Finset Nat) (e w a d : Nat → Nat)
    (boundary_supported : boundary ⊆ supported) (boundary_U : boundary ⊆ U)
    (departed_U : departed ⊆ U)
    (departed_iff : ∀ i ∈ U, i ∈ departed ↔ i ∉ supported)
    (stopped : ∀ i ∈ boundary ∪ departed, e i ≤ a i + d i)
    (retained : ∀ i ∈ U, i ∈ supported → i ∉ boundary → e i ≤ w i + d i) :
    (∑ i ∈ U, (e i - (if i ∈ supported then w i else 0))) +
      (∑ i ∈ boundary, w i) ≤
    (∑ i ∈ boundary ∪ departed, a i) + (∑ i ∈ U, d i) +
      (∑ i ∈ boundary, (w i - e i)) := by
  have subset : boundary ∪ departed ⊆ U := Finset.union_subset boundary_U departed_U
  have pointwise : ∀ i ∈ U,
      e i - (if i ∈ supported then w i else 0) + (if i ∈ boundary then w i else 0) ≤
      (if i ∈ boundary ∪ departed then a i else 0) + d i +
        (if i ∈ boundary then w i - e i else 0) := by
    intro i inside
    by_cases b : i ∈ boundary
    · have s := boundary_supported b
      have stop := stopped i (Finset.mem_union_left _ b)
      simp only [s, b, Finset.mem_union, true_or, ↓reduceIte]
      omega
    · by_cases s : i ∈ supported
      · have notDeparted : i ∉ departed := fun h => (departed_iff i inside).mp h s
        have keep := retained i inside s b
        simp only [s, b, notDeparted, Finset.mem_union, or_self, ↓reduceIte]
        omega
      · have dep := (departed_iff i inside).mpr s
        have stop := stopped i (Finset.mem_union_right _ dep)
        simp only [s, b, dep, Finset.mem_union, or_true, ↓reduceIte, Nat.sub_zero]
        exact stop
  have bound := Finset.sum_le_sum pointwise
  simpa only [Finset.sum_add_distrib, ← Finset.sum_filter,
    Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr boundary_U,
    Finset.inter_eq_right.mpr subset] using bound
structure Stop {x y : ForkedBeaconState preset} (tail : Run config checks x y) (i : Nat) where
  state : ForkedBeaconState preset
  pre : Run config checks x state
  post : Run config checks state y
  split : pre.append post = tail
  charge : Option DepartureCharge
  selected : match charge with
    | none => state = y ∧ ∀ c ∈ tail.departureCharges, c.index ≠ i
    | some c => c ∈ tail.departureCharges ∧ c.index = i ∧
        c.amount = effectiveAt state i ∧
        ∃ next, ∃ step : Step config checks state next,
          ∃ remaining : Run config checks next y,
            (pre.snoc step).append remaining = tail ∧ c ∈ step.departureCharges ∧
            ∃ v w, state.state.validators.data[i]? = some v ∧
              next.state.validators.data[i]? = some w ∧ v.exitEpoch = FAR_FUTURE_EPOCH ∧
              w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧ w.exitEpoch.toNat = c.epoch
private theorem Stop.selected_prefix_exit_unset {x y m : ForkedBeaconState preset}
    {tail : Run config checks x y} (stop : Stop tail i)
    (chosen : stop.charge = some c) (rest : Run config checks m stop.state)
    (v : Validator) (found : m.state.validators.data[i]? = some v) :
    v.exitEpoch = FAR_FUTURE_EPOCH := by
  have actual := stop.selected
  rw [chosen] at actual
  obtain ⟨next, step, remaining, fullSplit, occurs, before, after,
    atStop, atNext, unset, assigned, epoch⟩ := actual.2.2.2
  obtain ⟨last, located, kept⟩ := rest.registryLifecycle.validators i v found
  have same := Option.some.inj (located.symm.trans atStop)
  subst last
  by_contra set
  have fixed := kept.exitEpoch set
  exact set (fixed.symm.trans unset)
theorem Stop.selected_prefix_exit_gt {x y m : ForkedBeaconState preset}
    {tail : Run config checks x y} (stop : Stop tail i)
    (chosen : stop.charge = some c) (rest : Run config checks m stop.state)
    (v : Validator) (found : m.state.validators.data[i]? = some v)
    (finite : cutoff < FAR_FUTURE_EPOCH.toNat) : cutoff < v.exitEpoch.toNat := by
  rw [stop.selected_prefix_exit_unset chosen rest v found]
  exact finite
theorem prefix_exit_gt_of_endpoint
    {i cutoff : Nat}
    (rest : Run config checks m y) (v w : Validator)
    (before : m.state.validators.data[i]? = some v)
    (after : y.state.validators.data[i]? = some w)
    (retained : cutoff < w.exitEpoch.toNat) : cutoff < v.exitEpoch.toNat := by
  obtain ⟨last, found, life⟩ := rest.registryLifecycle.validators i v before
  have same := Option.some.inj (found.symm.trans after)
  subst last
  exact retained.trans_le (floor_exit_le life)
theorem Stop.exists {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (i : Nat) : Nonempty (Stop tail i) := by
  induction tail with
  | nil =>
    exact ⟨⟨x, .nil, .nil, rfl, none, by simp [Run.departureCharges]⟩⟩
  | @snoc middle last pre step ih =>
    obtain ⟨stop⟩ := ih
    cases chosen : stop.charge with
    | some c =>
      have selected := stop.selected
      rw [chosen] at selected
      obtain ⟨member, index, amount, next, assignedStep, rest, split, charged,
        v, w, before, after, unset, assigned, epoch⟩ := selected
      refine ⟨⟨stop.state, stop.pre, stop.post.snoc step,
        congrArg (fun r => r.snoc step) stop.split, some c, ?_⟩⟩
      exact ⟨List.mem_append_left _ member, index, amount, next, assignedStep,
        rest.snoc step, congrArg (fun r => r.snoc step) split, charged,
        v, w, before, after, unset, assigned, epoch⟩
    | none =>
      have absent := stop.selected
      rw [chosen] at absent
      by_cases latest : ∃ c ∈ step.departureCharges, c.index = i
      · obtain ⟨c, member, index⟩ := latest
        obtain ⟨⟨v, j⟩, present, added⟩ := List.mem_filterMap.mp member
        dsimp only at added
        split at added
        · cases added
        · rename_i w after
          split at added
          · rename_i exits
            cases Option.some.inj added
            change j = i at index
            subst j
            have before := List.mem_zipIdx_iff_getElem?.mp present
            rw [Array.getElem?_toList] at before
            simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at exits
            refine ⟨⟨middle, pre, Run.nil.snoc step, rfl,
              some ⟨i, w.exitEpoch.toNat, v.effectiveBalance.toNat⟩, ?_⟩⟩
            exact ⟨List.mem_append_right _ member, rfl,
              by simp [effectiveAt, before], last, step, .nil, rfl, member,
              v, w, before, after, exits.1, exits.2, rfl⟩
          · cases added
      · refine ⟨⟨last, pre.snoc step, .nil, rfl, none, rfl, ?_⟩⟩
        intro c member index
        rcases List.mem_append.mp member with prior | current
        · exact absent.2 c prior index
        · exact latest ⟨c, current, index⟩

end

end EthLib.Consensus.DirectSafety.Apriori.Internal
