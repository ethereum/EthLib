module

public import EthLib.Execution.Proofs.Evm.Call.CreatesPlain
public import EthLib.Execution.Proofs.Evm.Call.NonceOrCodeFreshSlots

/-!
# Proofs: the refund counter of a message pays back the slots that it clears

A message that succeeds gains at least the refund of each slot that it leaves cleared.

So a message that starts with no cleared slot ends with a counter of at least zero.

Source: [EIP-2200][eip2200], the refunds of net gas metering.

[eip2200]: https://eips.ethereum.org/EIPS/eip-2200#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256)
open EthLib.Execution.State (TransactionState)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The refund of a write -/

-- From Istanbul, a write that fills a cleared slot again takes back the refund of the clear.
--
-- So the refund counter of one frame can be negative.
--
-- EIP-3529 and EIP-8038 change the value of that refund, not the rule.

/-- The refund of a write that puts back the original word is never negative.

The price of a write that leaves a slot as it is stays below the price to set or reset a slot. -/
theorem sstoreReadCost_le (fork : Fork) :
    sstoreReadCost fork ≤ STORAGE_SET ∧ sstoreReadCost fork ≤ sstoreResetCost fork := by
  cases fork <;> decide

/-- The refund of a write covers the change in the refund of the slots that it clears.

It gains the refund of a clear when it clears a slot whose word before the transaction was not 0.

It loses it at most when it fills such a slot again. -/
theorem clear_le_sstoreRefund (original current new : U256) :
    ((gasSchedule fork).REFUND_STORAGE_CLEAR : Int) *
        ((if original ≠ 0 ∧ current ≠ 0 ∧ new = 0 then 1 else 0) -
          (if original ≠ 0 ∧ current = 0 ∧ new ≠ 0 then 1 else 0)) ≤
      sstoreRefund fork original current new := by
  obtain ⟨hset, hreset⟩ := sstoreReadCost_le fork
  have hclear : (0 : Int) ≤ (gasSchedule fork).REFUND_STORAGE_CLEAR := Int.natCast_nonneg _
  unfold sstoreRefund
  by_cases ho : original = 0 <;> by_cases hc : current = 0 <;> by_cases hn : new = 0 <;>
    by_cases hcn : current = new <;> by_cases hon : original = new <;>
    simp only [ho, hc, hn, hcn, hon, ne_eq, not_true_eq_false, not_false_eq_true, and_true,
      and_false, ↓reduceIte] at * <;>
    split_ifs <;> omega

/-! ## The refund that a frame holds beyond its cleared slots -/

/-- The refund of each slot that the state leaves cleared, at an account with a nonce or code. -/
def clearedRefund (fork : Fork) (state : TransactionState) : Int :=
  (gasSchedule fork).REFUND_STORAGE_CLEAR * (nonceOrCodeClearedSlots state).card

/-- The refund counter of a frame beyond the refund of the slots that its state leaves cleared. -/
def refundSurplus (evm : Evm fork Meter) : Int :=
  evm.substate.refundCounter - clearedRefund fork evm.state

/-- The second frame holds at least the refund surplus of the first.

That is asked only of a first frame whose account has a nonce or code.

The second frame then keeps a nonce or code at its account. -/
def RefundKept (a b : Evm fork Meter) : Prop :=
  HasNonceOrCode a.state a.message.currentTarget →
    HasNonceOrCode b.state b.message.currentTarget ∧ refundSurplus a ≤ refundSurplus b

omit [GasMeter Meter] in
/-- A step that keeps each nonce or code keeps the refund, when its surplus does not drop. -/
theorem RefundKept.of_keepsPlain {a b : Evm fork Meter} (hk : KeepsPlain a b)
    (hs : HasNonceOrCode a.state a.message.currentTarget → refundSurplus a ≤ refundSurplus b) :
    RefundKept a b :=
  fun hc => ⟨by rw [hk.1.2.1]; exact hk.1.1.1.2 _ hc, hs hc⟩

omit [GasMeter Meter] in
/-- A step that keeps each nonce or code, the refund counter and the cleared slots keeps the refund.
-/
theorem RefundKept.of_eq {a b : Evm fork Meter} (hk : KeepsPlain a b)
    (hr : b.substate.refundCounter = a.substate.refundCounter)
    (hs : nonceOrCodeClearedSlots b.state = nonceOrCodeClearedSlots a.state) : RefundKept a b :=
  .of_keepsPlain hk fun _ => by
    unfold refundSurplus clearedRefund
    rw [hr, hs]

/-- The rules of a frame keep the refund. -/
theorem frameStepRules_refundKept :
    FrameStepRules fork (RefundKept (fork := fork) (Meter := Meter)) where
  trans hab hbc hc :=
    have ⟨hb, h1⟩ := hab hc
    have ⟨hc', h2⟩ := hbc hb
    ⟨hc', h1.trans h2⟩
  static h := .of_eq (stepRules_keepsPlain.static h) h.refund
    (nonceOrCodeSlots_of_readsMore slotsOf_clearedSlots h.tracker)
  sstore evm key value state h := .of_keepsPlain (stepRules_keepsPlain.sstore evm key value state h)
    fun hc => by
      -- The cleared slots change at the written slot only, as the refund of the write covers.
      have hcard := card_nonceOrCodeSlots_setStorage slotsOf_clearedSlots hc h
      have hcl := TransactionState.card_clearedSlots_setStorage h
      have hge := clear_le_sstoreRefund (fork := fork)
        (evm.state.getStorageOriginal evm.message.currentTarget key)
        (evm.state.getStorage evm.message.currentTarget key) value
      unfold refundSurplus clearedRefund nonceOrCodeClearedSlots
      dsimp only [advance]
      generalize (if evm.state.getStorageOriginal evm.message.currentTarget key ≠ 0 ∧
        evm.state.getStorage evm.message.currentTarget key ≠ 0 ∧ value = 0 then (1 : Int)
          else 0) = i at hcl hge
      generalize (if evm.state.getStorageOriginal evm.message.currentTarget key ≠ 0 ∧
        evm.state.getStorage evm.message.currentTarget key = 0 ∧ value ≠ 0 then (1 : Int)
          else 0) = j at hcl hge
      have hdiff : ((nonceOrCodeSlots TransactionState.clearedSlots state).card : Int) -
          (nonceOrCodeSlots TransactionState.clearedSlots evm.state).card = i - j := by omega
      rw [← hdiff, Int.mul_sub] at hge
      omega
  tstore evm address key value := .of_eq (stepRules_keepsPlain.tstore evm address key value) rfl
    (nonceOrCodeSlots_setTransientStorage slotsOf_clearedSlots evm.state address key value)
  log log hs hsub hm hc := .of_eq (stepRules_keepsPlain.log log hs hsub hm hc)
    (by rw [hsub]) (by rw [hs])
  incrementNonce evm state hn h :=
    .of_keepsPlain (stepRules_keepsPlain.incrementNonce evm state hn h) fun hc => by
      unfold refundSurplus clearedRefund nonceOrCodeClearedSlots
      rw [nonceOrCodeSlots_incrementNonce slotsOf_clearedSlots hc h]

/-- The end of a successful SELFDESTRUCT keeps the refund: it adds a refund and clears no slot. -/
theorem refundKept_finishSelfdestruct {beneficiary : Address} {refund : Nat}
    {evm after : Evm fork Meter} (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    RefundKept evm after := by
  refine .of_keepsPlain (stepRules_keepsPlain.selfdestruct beneficiary refund h) fun _ => ?_
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
    cases h
    unfold refundSurplus clearedRefund nonceOrCodeClearedSlots
    rw [nonceOrCodeSlots_selfdestructTransfer slotsOf_clearedSlots (Base.mapError_ok_iff.mp hst)]
    dsimp only
    omega

/-! ## Messages -/

/-- A message from `state` and `substate` that ends with the frame `ended` pays for its clears.

When it succeeds, its counter rose by at least the refund of the slots that it clears.

When it fails, its state has the cleared slots of `state`. -/
def RefundEnds (state : TransactionState) (substate : Substate) (ended : Evm fork Meter) :
    Prop :=
  (ended.error = none →
    clearedRefund fork ended.state - clearedRefund fork state ≤
      ended.substate.refundCounter - substate.refundCounter) ∧
  (ended.error ≠ none → nonceOrCodeClearedSlots ended.state = nonceOrCodeClearedSlots state)

/-- A caller that takes in a message keeps the refund, when the message pays for its clears.

The message must keep each nonce or code of the caller. -/
theorem refundKept_incorporateChild {caller child : Evm fork Meter}
    (hk : KeepsNonceOrCode caller.state child.state)
    (hr : RefundEnds caller.state caller.substate.child child) :
    RefundKept caller (incorporateChild fork caller child) := by
  intro hc
  refine ⟨?_, ?_⟩
  · rw [message_incorporateChild, state_incorporateChild]
    exact hk.2 _ hc
  · unfold refundSurplus
    unfold incorporateChild
    split
    · -- A child that succeeds adds its counter, which started at zero.
      rename_i hok
      have := hr.1 (Option.isNone_iff_eq_none.mp hok)
      dsimp only [Substate.child, Substate.empty] at this ⊢
      omega
    · -- A child that fails leaves the cleared slots of its caller, and adds no refund.
      rename_i hfail
      have := hr.2 fun he => hfail (Option.isNone_iff_eq_none.mpr he)
      dsimp only
      unfold clearedRefund
      rw [this]

/-- What a call ends with, when its code runs only at an account with a nonce or code.

It keeps each nonce or code, the block, its message and the created accounts.

It pays for the slots that it clears. -/
def CallRefund (message : Message fork) (state : TransactionState) (substate : Substate)
    (meter : Meter) (ended : Evm fork Meter) : Prop :=
  (message.code.size ≠ 0 → HasNonceOrCode state message.currentTarget) →
    KeepsNonceOrCodeCall message state substate meter ended ∧ CreatesPlain state ended.state ∧
      RefundEnds state substate ended

/-- What a creation ends with, at an address with no nonce or code.

It keeps each nonce or code, the block and the created accounts, and pays for its clears. -/
def CreateRefund (message : Message fork) (state : TransactionState) (substate : Substate)
    (meter : Meter) (ended : Evm fork Meter) : Prop :=
  ¬HasNonceOrCode state message.currentTarget →
    (KeepsNonceOrCodeCreate message state substate meter ended ∧
      CreatesPlain state ended.state) ∧ RefundEnds state substate ended

/-- A frame related to an earlier one keeps each nonce or code, and holds at least its surplus.

The surplus is asked only of a frame that runs code only at an account with a nonce or code. -/
abbrev RefundFrame (a b : Evm fork Meter) : Prop :=
  KeepsPlain a b ∧ (CodeAtNonceOrCode a → refundSurplus a ≤ refundSurplus b)

/-- Every frame is related to itself. -/
theorem refundFrame_refl (evm : Evm fork Meter) : RefundFrame evm evm :=
  ⟨stepRules_keepsPlain.refl evm, fun _ => le_rfl⟩

/-- The frame relation is transitive. -/
theorem refundFrame_trans {a b c : Evm fork Meter} (hab : RefundFrame a b)
    (hbc : RefundFrame b c) : RefundFrame a c :=
  ⟨stepRules_keepsPlain.trans hab.1 hbc.1, fun ha =>
    (hab.2 ha).trans (hbc.2 (ha.keeps hab.1))⟩

/-- A static step is related to its frame. -/
theorem refundFrame_of_staticStep {a b : Evm fork Meter} (h : StaticStep a b) : RefundFrame a b :=
  ⟨stepRules_keepsPlain.static h, fun _ => by
    unfold refundSurplus clearedRefund nonceOrCodeClearedSlots
    rw [h.refund, nonceOrCodeSlots_of_readsMore slotsOf_clearedSlots h.tracker]⟩

omit [GasMeter Meter] in
/-- The relation of a frame gives the refund kept, at an account with a nonce or code. -/
private theorem refundFrame_of_refundKept {a b : Evm fork Meter} (hk : KeepsPlain a b)
    (hr : RefundKept a b) (hinv : CodeAtNonceOrCode a) (hcode : a.code.size ≠ 0) :
    RefundFrame a b :=
  ⟨hk, fun _ => (hr (hinv hcode)).2⟩

/-- The parts of a message that the caller takes in, by the kind of the message. -/
private abbrev ChildCall (message : Message fork) (state : TransactionState) (substate : Substate)
    (meter : Meter) (ended : Evm fork Meter) : Prop :=
  KeepsNonceOrCodeCall message state substate meter ended ∧ CreatesPlain state ended.state ∧
    RefundEnds state substate ended

/-- The parts of a creation that the caller takes in. -/
private abbrev ChildCreate (message : Message fork) (state : TransactionState) (substate : Substate)
    (meter : Meter) (ended : Evm fork Meter) : Prop :=
  (KeepsNonceOrCodeCreate message state substate meter ended ∧ CreatesPlain state ended.state) ∧
    RefundEnds state substate ended

/-- The parts of a message, of either kind, that the refund of the caller needs. -/
private abbrev ChildRefund (_ : Message fork) (state : TransactionState) (substate : Substate)
    (_ : Meter) (ended : Evm fork Meter) : Prop :=
  KeepsNonceOrCode state ended.state ∧ RefundEnds state substate ended

/-- Each step of a running frame keeps the frame relation.

The frame must run code only at an account with a nonce or code.

Each message it sends must end as a call or a creation does. -/
private theorem refundFrame_step {evm : Evm fork Meter} {result : StepResult fork Meter}
    (hinv : CodeAtNonceOrCode evm) (h : step fork evm = .ok result) :
    StepResult.Keeps RefundFrame (ChildRelByKind CallRefund CreateRefund) evm result := by
  have hs := stepRules_keepsPlain.step h
  by_cases hcode : evm.code.size = 0
  · -- A frame with no code stops at once.
    have hstop : result = .next (advance { evm with running := false }) := by
      unfold Evm.step at h
      split at h
      · omega
      · simp only [stopStep, Functor.map, Except.map, Except.ok.injEq] at h
        exact h.symm
    subst hstop
    exact ⟨hs, fun _ => le_rfl⟩
  have hr := frameStepRules_refundKept.step (C := fun caller message child =>
    ChildRefund message caller.state caller.substate.child
      (GasMeter.start message.gas message.reservoir) child)
    (fun hc => refundKept_incorporateChild hc.1 hc.2) h
  rcases hr with ⟨-, after, rfl, hsd⟩ | ⟨-, hr⟩
  · exact refundFrame_of_refundKept hs
      (frameStepRules_refundKept.selfdestructStep (fun _ _ h => refundKept_finishSelfdestruct h)
        hsd) hinv hcode
  cases result with
  | next after => exact refundFrame_of_refundKept hs hr hinv hcode
  | child caller message resume =>
    refine ⟨refundFrame_of_refundKept hs.1 hr.1 hinv hcode, fun child after resumed hchild => ?_⟩
    -- The message meets the hypothesis that its kind asks for.
    have hparts : ChildRelByKind ChildCall ChildCreate caller message child :=
      childRelByKind_of_step hinv h hs.1.1.1.1 hchild
    have hkeeps : ChildRelByKind KeepsNonceOrCodeCall KeepsNonceOrCodeCreate caller message child :=
      hparts.mono (fun _ _ _ _ _ hm => hm.1) fun _ _ _ _ _ hm => hm.1.1
    have hplain : CreatesPlain caller.state child.state := by
      have := hparts.mono (Mcall' := fun _ state _ _ ended => CreatesPlain state ended.state)
        (Mcreate' := fun _ state _ _ ended => CreatesPlain state ended.state)
        (fun _ _ _ _ _ hm => hm.2.1) fun _ _ _ _ _ hm => hm.1.2
      rwa [childRelByKind_self] at this
    have hrefund : ChildRefund message caller.state caller.substate.child
        (GasMeter.start message.gas message.reservoir) child := by
      have := hparts.mono (Mcall' := ChildRefund) (Mcreate' := ChildRefund)
        (fun _ _ _ _ _ hm => ⟨hm.1.1.1, hm.2.2⟩) fun _ _ _ _ _ hm => ⟨hm.1.1.1, hm.2⟩
      rwa [childRelByKind_self] at this
    exact ⟨⟨(keepsNonceOrCodeFrame_step h).2 child after resumed hkeeps,
        createsPlain_resume h resumed hs.1 hplain⟩,
      fun _ => ((hr.2 child after resumed hrefund) (hinv hcode)).2⟩

/-- The state that a message enters has the cleared slots of the state it is sent from.

Its substate has the refund counter of the substate it is sent from. -/
private theorem refund_entered {message : Message fork} {state entry : TransactionState}
    {substate entrySubstate : Substate}
    (h : Entered fork message state substate entry entrySubstate) :
    nonceOrCodeClearedSlots entry = nonceOrCodeClearedSlots state ∧
      entrySubstate.refundCounter = substate.refundCounter := by
  have hstart : nonceOrCodeClearedSlots (startState fork message state) =
      nonceOrCodeClearedSlots state := by
    unfold startState
    split
    · exact nonceOrCodeSlots_touchAccount slotsOf_clearedSlots _ _
    · rfl
  rcases h with ⟨-, rfl, rfl⟩ | ⟨-, hm, rfl⟩
  · exact ⟨hstart, rfl⟩
  · exact ⟨(nonceOrCodeSlots_moveEther slotsOf_clearedSlots hm).trans hstart, rfl⟩

/-- A call ends as it should, once its frame ends related to its start frame. -/
private theorem callRefund_rollbackOnError {message : Message fork}
    {state entry : TransactionState} {substate entrySubstate : Substate} {meter : Meter}
    {ended : Evm fork Meter}
    (hentry : Entered fork message state substate entry entrySubstate)
    (hrun : CodeAtNonceOrCode (startFrame message entry entrySubstate meter) →
      RefundFrame (startFrame message entry entrySubstate meter) ended) :
    CallRefund message state substate meter (rollbackOnError state ended) := by
  intro hcode
  have kentry := keepsNonceOrCode_entered hentry
  have hinv : CodeAtNonceOrCode (startFrame message entry entrySubstate meter) :=
    fun hs => kentry.2 _ (hcode hs)
  obtain ⟨⟨hframe, hc⟩, hsurplus⟩ := hrun hinv
  -- The call keeps each nonce or code and the block, as every call does.
  have kcall := keepsNonceOrCodeCall_rollbackOnError (meter := meter) hentry hframe
  have cplain : CreatesPlain state ended.state :=
    CreatesPlain.trans kentry (createsPlain_of_eq (createdAccounts_entered hentry)) hc
  have hpar : ended.state.parent = state.parent := hframe.1.2.trans (parent_entered hentry)
  obtain ⟨hslots, hsub⟩ := refund_entered hentry
  refine ⟨kcall, cplain.of_created (createdAccounts_rollbackOnError state ended).1, ?_, ?_⟩
  · -- A frame that succeeds keeps its state, and its surplus did not drop.
    intro herr
    have hne : ended.error = none := by
      unfold rollbackOnError at herr
      split at herr <;> exact herr
    have hE : rollbackOnError state ended = ended := by
      unfold rollbackOnError
      simp [hne]
    rw [hE]
    have := hsurplus hinv
    unfold refundSurplus at this
    dsimp only [startFrame] at this
    unfold clearedRefund at this ⊢
    rw [hslots, hsub] at this
    omega
  · -- A frame that fails puts back the state, whose cleared slots are those of the start.
    intro herr
    have herr' : ended.error ≠ none := by
      intro he
      apply herr
      unfold rollbackOnError
      simp [he]
    unfold rollbackOnError
    simp only [Option.isSome_iff_ne_none.mpr herr', ↓reduceIte]
    exact nonceOrCodeSlots_restoreTxState slotsOf_clearedSlots (hpar) cplain.1 cplain.2

/-- The frame that ends a creation, after the deposit of code.

It may put back the state, with an error.

It may keep the state, the substate and no error, and may then store the code. -/
private theorem depositCode_refund {snapshot : TransactionState} {evm after : Evm fork Meter}
    (h : depositCode fork snapshot evm = .ok after) :
    (after.state = evm.state.restoreTxState snapshot ∧ after.error ≠ none) ∨
      (evm.error = none ∧ after.error = none ∧ after.substate = evm.substate ∧
        (after.state = evm.state ∨
          evm.state.setCode fork evm.message.currentTarget evm.output = .ok after.state)) := by
  unfold depositCode at h
  dsimp only at h
  split at h
  · rename_i hs
    cases h
    exact .inl ⟨rfl, Option.isSome_iff_ne_none.mp hs⟩
  rename_i hok
  have hnone : evm.error = none := by simpa using hok
  split at h
  · cases h
    exact .inl ⟨rfl, by simp⟩
  split at h
  · cases h
    exact .inl ⟨rfl, by simp⟩
  split at h
  · cases h
    split
    · exact .inl ⟨rfl, by simp⟩
    · exact .inr ⟨hnone, hnone, rfl, .inl rfl⟩
  split at h
  · cases h
    exact .inl ⟨rfl, by simp⟩
  obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact .inr ⟨hnone, hnone, rfl, .inr (Base.mapError_ok_iff.mp hst)⟩

/-- From Spurious Dragon, a creation ends as it should, once its init code ends as a call does. -/
private theorem createRefund_depositCode (hfork : .spuriousDragon ≤ fork)
    {message : Message fork} {state prepared : TransactionState} {substate : Substate}
    {meter : Meter} {evm after : Evm fork Meter}
    (hp : prepareCreation fork state message.currentTarget = .ok prepared)
    (hm : CallRefund message prepared substate meter evm)
    (hd : depositCode fork state evm = .ok after) :
    CreateRefund message state substate meter after := by
  intro hnc
  -- The start of the creation gives the address a nonce.
  have hnonce : 1 ≤ (prepared.getAccount message.currentTarget).nonce := by
    unfold prepareCreation at hp
    simp only [show fork ≥ .spuriousDragon from hfork, ↓reduceIte] at hp
    rw [(TransactionState.getAccount_incrementNonce (Base.mapError_ok_iff.mp hp)).1]
    exact Nat.succ_le_of_lt (Nat.succ_pos _)
  obtain ⟨kcall, hc, hends⟩ := hm (fun _ => .inl hnonce)
  have kcreate := keepsNonceOrCodeCreate_depositCode hfork hp kcall hd
  obtain ⟨⟨hk, hpar⟩, hmsg⟩ := kcall
  have kprep := keepsNonceOrCode_prepareCreation hp
  have cevm : CreatesPlain state evm.state :=
    CreatesPlain.trans kprep (createsPlain_prepareCreation hnc hp) hc
  have pevm : evm.state.parent = state.parent := hpar.trans (parent_prepareCreation hp)
  have hprep : nonceOrCodeClearedSlots prepared = nonceOrCodeClearedSlots state :=
    nonceOrCodeSlots_prepareCreation slotsOf_clearedSlots (fun h => h.1 rfl) hnc hp
  rcases depositCode_refund hd with ⟨hs, herr⟩ | ⟨hevm, herr, hsub, hs⟩
  · -- A failed creation puts back the state.
    refine ⟨⟨kcreate, ?_⟩, fun he => absurd he herr, fun _ => ?_⟩
    · rw [hs]
      exact cevm.of_created rfl
    · rw [hs]
      exact nonceOrCodeSlots_restoreTxState slotsOf_clearedSlots pevm cevm.1 cevm.2
  · have hrefund := hends.1 hevm
    unfold clearedRefund at hrefund
    rw [hprep] at hrefund
    -- The code goes to the address, which keeps its nonce, so the cleared slots stay.
    have hafter : nonceOrCodeClearedSlots after.state = nonceOrCodeClearedSlots evm.state := by
      rcases hs with hs | hs
      · rw [hs]
      · have hnonce_evm : 1 ≤ (evm.state.getAccount evm.message.currentTarget).nonce := by
          rw [hmsg]
          exact Nat.le_trans hnonce (hk.1 message.currentTarget)
        exact nonceOrCodeSlots_setCode slotsOf_clearedSlots hnonce_evm hs
    refine ⟨⟨kcreate, ?_⟩, fun _ => ?_, fun he => absurd herr he⟩
    · rcases hs with hs | hs
      · rw [hs]
        exact cevm
      · exact cevm.of_created (TransactionState.createdAccounts_setCode hs)
    · unfold clearedRefund
      rw [hafter, hsub]
      exact hrefund

/-- From Spurious Dragon, by induction on gas, every call and creation ends as it should. -/
private theorem refund_induction [LawfulGasMeter Meter] (hfork : .spuriousDragon ≤ fork)
    (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate)
      (meter : Meter) (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        CallRefund message state substate meter ended.val) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate)
      (meter : Meter) (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        CreateRefund message state substate meter ended.val) :=
  -- The proof is by strong induction on the gas of the message, for calls and creations together.
  processMessage_frame_byKind
    (F := fun a b => CodeAtNonceOrCode a → RefundFrame a b)
    (Mcall := CallRefund) (Mcreate := CreateRefund)
    (fun runs _ h hinv =>
      rel_runFrame refundFrame_refl refundFrame_trans (fun ha hab => ha.keeps hab.1)
        (fun evm error _ => refundFrame_of_staticStep (staticStep_exceptionalHalt evm error))
        (fun hinv _ h => refundFrame_step hinv h)
        (fun caller message lt ended _ hran => runs caller message lt ended hran) hinv h)
    (fun _ _ _ _ => refundFrame_of_staticStep (.of_sameContext ⟨rfl, rfl, rfl, rfl⟩))
    (fun _ _ hrp _ => refundFrame_of_staticStep (staticStep_runPrecompile hrp))
    (fun hentry hrun => callRefund_rollbackOnError hentry hrun)
    (fun hp hm hd => createRefund_depositCode hfork hp hm hd) n

/-- From Spurious Dragon, a call that succeeds gains at least the refund of the slots it clears.

The clears counted are the slots it leaves cleared at accounts with a nonce or code.

When it has code, its current account must have a nonce or code. -/
theorem processMessage_clearedRefund_le [LawfulGasMeter Meter] (hfork : .spuriousDragon ≤ fork)
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (hcode : message.code.size ≠ 0 → HasNonceOrCode state message.currentTarget)
    (h : processMessage fork message state substate meter held = .ok ended)
    (hok : ended.val.error = none) :
    clearedRefund fork ended.val.state - clearedRefund fork state ≤
      ended.val.substate.refundCounter - substate.refundCounter :=
  ((refund_induction hfork message.gas).1 message state substate meter held rfl ended h
    hcode).2.2.1 hok

/-- From Spurious Dragon, a creation that succeeds gains at least the refund of the slots it clears.

Its address must have no nonce or code. -/
theorem processCreateMessage_clearedRefund_le [LawfulGasMeter Meter]
    (hfork : .spuriousDragon ≤ fork) {message : Message fork} {state : TransactionState}
    {substate : Substate} {meter : Meter} {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (hcode : ¬HasNonceOrCode state message.currentTarget)
    (h : processCreateMessage fork message state substate meter held = .ok ended)
    (hok : ended.val.error = none) :
    clearedRefund fork ended.val.state - clearedRefund fork state ≤
      ended.val.substate.refundCounter - substate.refundCounter :=
  ((refund_induction hfork message.gas).2 message state substate meter held rfl ended h
    hcode).2.1 hok

/-! ## Before Istanbul -/

/-- Before Istanbul, a write gives back a refund of at least zero. -/
theorem sstoreRefund_nonneg (hfork : fork < .istanbul) (original current new : U256) :
    0 ≤ sstoreRefund fork original current new := by
  have hpre : ¬fork ≥ .istanbul := Nat.not_le.mpr hfork
  unfold sstoreRefund
  simp only [hpre, ↓reduceIte]
  split_ifs <;> omega

/-- The second frame holds at least the refund counter of the first. -/
private abbrev CounterLe (a b : Evm fork Meter) : Prop :=
  a.substate.refundCounter ≤ b.substate.refundCounter

/-- A message from `substate` that succeeds ends with at least the counter of `substate`. -/
private abbrev CounterEnds (_ : Message fork) (_ : TransactionState) (substate : Substate)
    (_ : Meter) (ended : Evm fork Meter) : Prop :=
  ended.error = none → substate.refundCounter ≤ ended.substate.refundCounter

omit [GasMeter Meter] in
/-- Before Istanbul, the rules of a frame never lower the refund counter. -/
private theorem frameStepRules_counterLe (hfork : fork < .istanbul) :
    FrameStepRules fork (CounterLe (fork := fork) (Meter := Meter)) where
  trans hab hbc := Int.le_trans hab hbc
  static h := Int.le_of_eq h.refund.symm
  sstore _ _ _ _ _ := Int.le_add_of_nonneg_right (sstoreRefund_nonneg hfork _ _ _)
  tstore _ _ _ _ := Int.le_refl _
  log _ _ hsub _ _ := by rw [CounterLe, hsub]
  incrementNonce _ _ _ _ := Int.le_refl _

/-- Before Istanbul, a message that succeeds ends with at least the counter it starts from.

That holds of a call and of a creation, and for every state. -/
private theorem counter_induction [LawfulGasMeter Meter] (hfork : fork < .istanbul) (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        CounterEnds message state substate meter ended.val) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        CounterEnds message state substate meter ended.val) := by
  have T := frameStepRules_counterLe (Meter := Meter) hfork
  -- A child starts from a counter of zero, and a caller adds its counter only when it succeeds.
  have inc : ∀ {caller : Evm fork Meter} {message : Message fork} {child : Evm fork Meter},
      ChildRel CounterEnds caller message child →
        CounterLe caller (incorporateChild fork caller child) := by
    intro caller message child hc
    unfold incorporateChild
    split
    · rename_i hok
      have := hc (Option.isNone_iff_eq_none.mp hok)
      dsimp only [Substate.child, Substate.empty] at this
      show caller.substate.refundCounter ≤
        caller.substate.refundCounter + child.substate.refundCounter
      omega
    · exact Int.le_refl _
  refine processMessage_rel (Inv := fun _ => True) T.refl T.trans (fun _ _ => trivial)
    (fun evm error _ => T.static (staticStep_exceptionalHalt evm error)) (fun _ h => ?_)
    (fun _ _ => T.sameContext ⟨rfl, rfl, rfl, rfl⟩)
    (fun h _ => T.static (staticStep_runPrecompile h)) (fun hentry hrun => ?_)
    (fun _ hm hd => ?_) n
  · rcases T.step inc h with ⟨-, after, rfl, hsd⟩ | ⟨-, keeps⟩
    · refine T.selfdestructStep (fun _ refund h => ?_) hsd
      unfold finishSelfdestruct at h
      split at h
      · cases h
      · obtain ⟨st, -, h⟩ := Base.bind_ok_iff.mp h
        cases h
        exact Int.le_add_of_nonneg_right (Int.natCast_nonneg refund)
    · exact keeps
  · -- A rollback keeps the substate, whose counter started at that of the caller's substate.
    intro _
    rw [(createdAccounts_rollbackOnError _ _).2]
    have := hrun trivial
    obtain ⟨-, hsub⟩ := refund_entered hentry
    dsimp only [CounterLe, startFrame] at this
    omega
  · -- A creation that succeeds had an init code that succeeded, and keeps its substate.
    intro herr
    rcases depositCode_refund hd with ⟨-, hfail⟩ | ⟨hevm, -, hsub, -⟩
    · exact absurd herr hfail
    · rw [hsub]
      exact hm hevm

/-- Before Istanbul, a call that succeeds ends with at least the refund counter it starts from. -/
theorem processMessage_refundCounter_le_of_lt_istanbul [LawfulGasMeter Meter]
    (hfork : fork < .istanbul) {message : Message fork} {state : TransactionState}
    {substate : Substate} {meter : Meter} {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended)
    (hok : ended.val.error = none) :
    substate.refundCounter ≤ ended.val.substate.refundCounter :=
  (counter_induction hfork message.gas).1 message state substate meter held rfl ended h hok

/-- Before Istanbul, a creation that succeeds ends with at least the refund counter it starts from.
-/
theorem processCreateMessage_refundCounter_le_of_lt_istanbul [LawfulGasMeter Meter]
    (hfork : fork < .istanbul) {message : Message fork} {state : TransactionState}
    {substate : Substate} {meter : Meter} {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processCreateMessage fork message state substate meter held = .ok ended)
    (hok : ended.val.error = none) :
    substate.refundCounter ≤ ended.val.substate.refundCounter :=
  (counter_induction hfork message.gas).2 message state substate meter held rfl ended h hok

end EthLib.Execution.Evm
