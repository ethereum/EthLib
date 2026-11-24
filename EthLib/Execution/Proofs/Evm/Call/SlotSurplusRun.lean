module

public import EthLib.Execution.Proofs.Evm.Call.MeterRules
public import EthLib.Execution.Proofs.Evm.Call.NonceOrCode
public import EthLib.Execution.Proofs.Evm.Call.SlotSurplusCalls
public import EthLib.Execution.Proofs.Evm.Call.ToDelete

/-!
# Proofs: from Glamsterdam, a call or a creation pays for the slots it counts

The counted slots are the fresh slots of the accounts with a nonce or code.

A call must run code only at an account with a nonce or code.

A creation must start at an address with no nonce or code, and each nested creation does.

Source: [EIP-8037][eip8037], its reservoir model and its accounting for halts and reverts.

[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork}

/-- The second state keeps every account that the first created.

Each account that it creates beyond those has no nonce or code in the first state. -/
private def CreatesPlain (tx tx' : TransactionState) : Prop :=
  (∀ address, address ∈ tx.createdAccounts → address ∈ tx'.createdAccounts) ∧
    ∀ address, address ∈ tx'.createdAccounts → address ∉ tx.createdAccounts →
      ¬HasNonceOrCode tx address

/-! ## Created accounts with no nonce or code -/

/-- Two states with the same created accounts are related. -/
private theorem createsPlain_of_eq {tx tx' : TransactionState}
    (h : tx'.createdAccounts = tx.createdAccounts) : CreatesPlain tx tx' :=
  ⟨fun _ hx => h ▸ hx, fun _ hx hn => absurd (h ▸ hx) hn⟩

/-- The relation passes to a later state with the same created accounts. -/
private theorem CreatesPlain.of_created {tx tx' tx'' : TransactionState}
    (h : CreatesPlain tx tx') (hc : tx''.createdAccounts = tx'.createdAccounts) :
    CreatesPlain tx tx'' :=
  ⟨fun a ha => hc ▸ h.1 a ha, fun a ha hn => h.2 a (hc ▸ ha) hn⟩

/-- The relation composes when the first transition keeps each nonce or code.

An account with no nonce or code in the middle state had none in the first. -/
private theorem CreatesPlain.trans {a b c : TransactionState} (hk : KeepsNonceOrCode a b)
    (hab : CreatesPlain a b) (hbc : CreatesPlain b c) : CreatesPlain a c := by
  refine ⟨fun x hx => hbc.1 x (hab.1 x hx), fun x hx hxa => ?_⟩
  by_cases hxb : x ∈ b.createdAccounts
  · exact hab.2 x hxb hxa
  · exact fun hn => hbc.2 x hx hxb (hk.2 x hn)

/-- The start of a creation at an address with no nonce or code is related to the state before. -/
private theorem createsPlain_prepareCreation {state prepared : TransactionState}
    {address : Address} (hnc : ¬HasNonceOrCode state address)
    (h : prepareCreation fork state address = .ok prepared) : CreatesPlain state prepared := by
  -- The start records the address as created, and creates no other account.
  have hc : prepared.createdAccounts = state.createdAccounts.insert address := by
    unfold prepareCreation at h
    split at h
    · exact (TransactionState.createdAccounts_modifyState (Base.mapError_ok_iff.mp h)).trans rfl
    · cases h
      rfl
  refine ⟨fun x hx => hc ▸ Std.ExtTreeSet.mem_insert.mpr (.inr hx), fun x hx hxs => ?_⟩
  rw [hc] at hx
  rcases Std.ExtTreeSet.mem_insert.mp hx with heq | hx
  · cases Std.LawfulEqCmp.eq_of_compare heq
    exact hnc
  · exact absurd hx hxs

/-- The end of a successful SELFDESTRUCT keeps the created accounts. -/
private theorem createdAccounts_finishSelfdestruct {beneficiary : Address} {refund : Nat}
    {evm after : Evm fork StateGasMeter}
    (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    after.state.createdAccounts = evm.state.createdAccounts := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact createdAccounts_selfdestructTransfer (Base.mapError_ok_iff.mp hst)

/-! ## The frame relation -/

/-- What a step keeps of the state: each nonce or code and the block, and the created accounts.

It also keeps the message and the code. -/
private abbrev StateRel (a b : Evm fork StateGasMeter) : Prop :=
  KeepsNonceOrCodeFrame a b ∧ CreatesPlain a.state b.state

/-- Each write of a step keeps the state relation.

The proof that steps keep each nonce or code gives the first half. -/
private theorem stepRules_state : StepRules fork (StateRel (fork := fork)) where
  trans hab hbc := ⟨stepRules_keepsNonceOrCodeFrame.trans hab.1 hbc.1,
    CreatesPlain.trans hab.1.1.1 hab.2 hbc.2⟩
  static h := ⟨stepRules_keepsNonceOrCodeFrame.static h, createsPlain_of_eq h.created⟩
  sstore evm address key value state gain h :=
    ⟨stepRules_keepsNonceOrCodeFrame.sstore evm address key value state gain h,
      createsPlain_of_eq (TransactionState.createdAccounts_setStorage h)⟩
  tstore evm address key value :=
    ⟨stepRules_keepsNonceOrCodeFrame.tstore evm address key value, createsPlain_of_eq rfl⟩
  log log hs hsub hm hc :=
    ⟨stepRules_keepsNonceOrCodeFrame.log log hs hsub hm hc, createsPlain_of_eq (by rw [hs])⟩
  selfdestruct beneficiary refund h :=
    ⟨stepRules_keepsNonceOrCodeFrame.selfdestruct beneficiary refund h,
      createsPlain_of_eq (createdAccounts_finishSelfdestruct h)⟩
  incrementNonce evm address state hn h :=
    ⟨stepRules_keepsNonceOrCodeFrame.incrementNonce evm address state hn h,
      createsPlain_of_eq (TransactionState.createdAccounts_modifyState h)⟩
  incorporate h :=
    ⟨stepRules_keepsNonceOrCodeFrame.incorporate h.1, by rw [state_incorporateChild]; exact h.2⟩

/-- The meter keeps its starting reservoir, its committed spill and its baseline. -/
private abbrev MeterKept (a b : StateGasMeter) : Prop :=
  b.grant = a.grant ∧ b.committed = a.committed ∧ b.baseline = a.baseline

/-- Each operation that a frame applies keeps the starting reservoir, the spill and the baseline.

Only a commit changes the baseline, and no frame applies one. -/
private theorem meterRules_kept : MeterRules MeterKept where
  refl _ := ⟨rfl, rfl, rfl⟩
  trans hab hbc := ⟨hbc.1.trans hab.1, hbc.2.1.trans hab.2.1, hbc.2.2.trans hab.2.2⟩
  charge {meter after amount} h := by
    simp only [GasMeter.charge, StateGasMeter.charge] at h
    split at h
    · cases h
    · cases h
      exact ⟨rfl, rfl, rfl⟩
  chargeState {meter after amount} h := by
    simp only [GasMeter.chargeState, StateGasMeter.chargeState] at h
    split at h
    · cases h
      exact ⟨rfl, rfl, rfl⟩
    · split at h
      · cases h
        exact ⟨rfl, rfl, rfl⟩
      · cases h
  refill _ _ := ⟨rfl, rfl, rfl⟩
  exhaust _ := ⟨rfl, rfl, rfl⟩
  rollback _ := ⟨rfl, rfl, rfl⟩
  drain _ := ⟨rfl, rfl, rfl⟩
  credit _ _ _ := ⟨rfl, rfl, rfl⟩
  absorb _ _ succeeded := by
    cases succeeded <;> exact ⟨rfl, rfl, rfl⟩

/-- A frame related to an earlier one keeps its state and its meter, and pays for its slots. -/
private abbrev FrameRel (a b : Evm fork StateGasMeter) : Prop :=
  StateRel a b ∧ MeterKept a.gas b.gas ∧ PaysSlots a b

/-- A frame runs its code only at an account with a nonce or code. -/
private abbrev FrameInv (evm : Evm fork StateGasMeter) : Prop :=
  evm.code.size ≠ 0 → HasNonceOrCode evm.state evm.message.currentTarget

/-- Every frame is related to itself. -/
private theorem frameRel_refl (evm : Evm fork StateGasMeter) : FrameRel evm evm :=
  ⟨stepRules_state.refl evm, meterRules_kept.refl _, PaysSlots.refl evm⟩

/-- The frame relation is transitive. -/
private theorem frameRel_trans {a b c : Evm fork StateGasMeter} (hab : FrameRel a b)
    (hbc : FrameRel b c) : FrameRel a c :=
  ⟨stepRules_state.trans hab.1 hbc.1, meterRules_kept.trans hab.2.1 hbc.2.1,
    hab.2.2.trans hbc.2.2⟩

/-- A related frame keeps the invariant. -/
private theorem frameInv_keeps {a b : Evm fork StateGasMeter} (ha : FrameInv a)
    (hab : FrameRel a b) : FrameInv b := by
  intro hs
  rw [hab.1.1.2.1]
  exact hab.1.1.1.1.2 _ (ha (hab.1.1.2.2 ▸ hs))

/-- An exceptional halt is related to the frame it halts. -/
private theorem frameRel_halt (evm : Evm fork StateGasMeter) (error : EvmError) :
    FrameRel evm (exceptionalHalt evm error) :=
  ⟨stepRules_state.static (staticStep_exceptionalHalt _ _), meterRules_kept.exhaust _,
    paysSlots_exceptionalHalt _ _ _⟩

/-! ## Messages -/

/-- What a call ends with, when its code runs only at an account with a nonce or code.

It keeps its message, each nonce or code, the created accounts, the block and the baseline.

When it fails, its net state gas is that of its meter rolled back.

It pays for its slots. -/
private def CallPays (message : Message fork) (state : TransactionState) (substate : Substate)
    (meter : StateGasMeter) (ended : Evm fork StateGasMeter) : Prop :=
  (message.code.size ≠ 0 → HasNonceOrCode state message.currentTarget) →
    KeepsNonceOrCodeCall message state substate meter ended ∧
      CreatesPlain state ended.state ∧
      ended.gas.baseline = meter.baseline ∧
      (ended.error ≠ none → ended.gas.stateGasUsed = meter.restore.stateGasUsed) ∧
      MessagePays message state substate meter ended

/-- What a creation ends with, at an address with no nonce or code.

It keeps each nonce or code, the created accounts and the block, and pays for its slots. -/
private def CreatePays (message : Message fork) (state : TransactionState) (substate : Substate)
    (meter : StateGasMeter) (ended : Evm fork StateGasMeter) : Prop :=
  ¬HasNonceOrCode state message.currentTarget →
    (KeepsNonceOrCodeCreate message state substate meter ended ∧
      CreatesPlain state ended.state) ∧ MessagePays message state substate meter ended

/-- A step that sends a message runs code. -/
private theorem code_size_ne_zero_of_step_child {evm caller : Evm fork StateGasMeter}
    {message : Message fork}
    {resume : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    (h : step fork evm = .ok (.child caller message resume)) : evm.code.size ≠ 0 := by
  unfold Evm.step at h
  split at h
  · omega
  · simp only [stopStep, Functor.map, Except.map, Except.ok.injEq] at h
    cases h

/-- A message that a step sends ends related to its caller, and pays for its slots.

The step must run code only at an account with a nonce or code. -/
private theorem child_pays {evm caller child : Evm fork StateGasMeter} {message : Message fork}
    {resume : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    (hinv : FrameInv evm) (h : step fork evm = .ok (.child caller message resume))
    (hcaller : KeepsNonceOrCode evm.state caller.state)
    (hchild : ChildRelByKind CallPays CreatePays caller message child) :
    ChildRelByKind KeepsNonceOrCodeCall KeepsNonceOrCodeCreate caller message child ∧
      CreatesPlain caller.state child.state ∧ ChildRel MessagePays caller message child := by
  have hcur : HasNonceOrCode evm.state evm.message.currentTarget :=
    hinv (code_size_ne_zero_of_step_child h)
  unfold ChildRelByKind ChildRel at hchild ⊢
  rcases ht : message.target with _ | target
  · -- A creation goes to an address with no nonce or code in the state of its caller.
    simp only [ht] at hchild ⊢
    obtain ⟨hn0, hc0, -⟩ := TransactionState.accountDeployable_eq_true_iff.mp
      (accountDeployable_of_create_step hcur h ht).1
    obtain ⟨⟨hk, hc⟩, hp⟩ := hchild fun hnc => hnc.elim (fun hn => by omega) (fun hc => hc hc0)
    exact ⟨hk, hc, hp⟩
  · -- A call runs at the current account, or runs code only at an account with code.
    simp only [ht] at hchild ⊢
    have hcode : message.code.size ≠ 0 → HasNonceOrCode caller.state message.currentTarget := by
      intro hne
      rcases step_eq_child_staticCode h (by simp [ht]) with heq | hstatic
      · rw [heq]
        exact hcaller.2 _ hcur
      · exact hcaller.2 _ (.inr (hstatic hne))
    obtain ⟨hk, hc, -, -, hp⟩ := hchild hcode
    exact ⟨hk, hc, hp⟩

/-- The frame that resumes after a message keeps the created accounts from the frame before.

That needs the caller to keep each nonce or code of the frame before. -/
private theorem createsPlain_resume {evm caller child after : Evm fork StateGasMeter}
    {message : Message fork}
    {resume : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    (h : step fork evm = .ok (.child caller message resume)) (resumed : resume child = .ok after)
    (hcaller : StateRel evm caller) (hchild : CreatesPlain caller.state child.state) :
    CreatesPlain evm.state after.state := by
  -- The frame that resumes has the state of the child.
  have hs : after.state = child.state :=
    (sameContext_of_step_eq_child h resumed).state.trans (state_incorporateChild caller child)
  rw [hs]
  exact CreatesPlain.trans hcaller.1.1.1 hcaller.2 hchild

/-- From Glamsterdam, each step of a running frame keeps the frame relation.

The frame must run code only at an account with a nonce or code.

Each message it sends must end as a call or a creation does. -/
private theorem frameRel_step (hfork : .glamsterdam ≤ fork) {evm : Evm fork StateGasMeter}
    {result : StepResult fork StateGasMeter} (hinv : FrameInv evm) (running : evm.running = true)
    (h : step fork evm = .ok result) :
    StepResult.Keeps FrameRel (ChildRelByKind CallPays CreatePays) evm result := by
  have hs := stepRules_state.step h
  have hm := meterRules_kept.step (C := fun _ _ _ => True) h
  -- Each step of the frame pays, given what the messages it sends pay.
  have hp := paysSlots_step hfork running hinv h
  cases result with
  | next after => exact ⟨hs, hm, hp⟩
  | child caller message resume =>
    refine ⟨⟨hs.1, hm.1, hp.1⟩, fun child after resumed hchild => ?_⟩
    obtain ⟨hk, hc, hpay⟩ := child_pays hinv h hs.1.1.1.1 hchild
    exact ⟨⟨(keepsNonceOrCodeFrame_step h).2 child after resumed hk,
        createsPlain_resume h resumed hs.1 hc⟩,
      hm.2 child after resumed trivial, hp.2 child after resumed hpay⟩

/-- A precompile pays for its slots from a frame with no error. -/
private theorem paysSlots_runPrecompile {address : Nat} {evm after : Evm fork StateGasMeter}
    (herr : evm.error = none) (h : runPrecompile fork address evm = some after) :
    PaysSlots evm after := by
  unfold runPrecompile at h
  split at h
  · cases h
  · cases h
    exact paysSlots_exceptionalHalt _ _ _
  · split at h
    · cases h
      exact paysSlots_exceptionalHalt _ _ _
    · rename_i hc
      cases h
      -- A charge of execution gas keeps the net state gas.
      exact Or.inr ⟨fun hf => hf.2.1 herr, fun _ =>
        ⟨herr, by unfold slotSurplus; rw [StateGasMeter.stateGasUsed_charge hc]⟩⟩

/-- The state that a message enters counts the slots of the state it is sent from. -/
private theorem nonceOrCodeFreshSlots_entered {message : Message fork}
    {state entry : TransactionState} {substate entrySubstate : Substate}
    (h : Entered fork message state substate entry entrySubstate) :
    nonceOrCodeFreshSlots entry = nonceOrCodeFreshSlots state := by
  have hstart : nonceOrCodeFreshSlots (startState fork message state) =
      nonceOrCodeFreshSlots state := by
    unfold startState
    split
    · exact nonceOrCodeFreshSlots_touchAccount _ _
    · rfl
  rcases h with ⟨-, rfl, -⟩ | ⟨-, hm, -⟩
  · exact hstart
  · exact (nonceOrCodeFreshSlots_moveEther hm).trans hstart

/-- Two meters with the same starting reservoir, committed spill and baseline roll back alike. -/
private theorem stateGasUsed_restore_congr {a b : StateGasMeter} (h : MeterKept a b) :
    b.restore.stateGasUsed = a.restore.stateGasUsed := by
  simp only [StateGasMeter.restore, StateGasMeter.stateGasUsed, h.1, h.2.1, h.2.2]

/-- A failed frame, once rolled back, has the net state gas of its meter rolled back. -/
private theorem stateGasUsed_rollbackOnError_of_failed {snapshot : TransactionState}
    {ended : Evm fork StateGasMeter} (hf : FailedFrame ended) :
    (rollbackOnError snapshot ended).gas.stateGasUsed = ended.gas.restore.stateGasUsed := by
  obtain ⟨-, herr, hrev⟩ := hf
  unfold rollbackOnError
  simp only [Option.isSome_iff_ne_none.mpr herr, ↓reduceIte]
  rcases hrev with hrev | ⟨hspill, hres⟩
  · simp only [hrev, ↓reduceIte]
    rfl
  · split
    · rfl
    · simp only [StateGasMeter.stateGasUsed, StateGasMeter.restore, hspill, hres]

/-- A call ends as it should, once its frame ends related to its start frame. -/
private theorem callPays_rollbackOnError {message : Message fork}
    {state entry : TransactionState} {substate entrySubstate : Substate} {meter : StateGasMeter}
    {ended : Evm fork StateGasMeter}
    (hentry : Entered fork message state substate entry entrySubstate)
    (hrun : FrameInv (startFrame message entry entrySubstate meter) →
      (startFrame message entry entrySubstate meter).error = none →
      FrameRel (startFrame message entry entrySubstate meter) ended) :
    CallPays message state substate meter (rollbackOnError state ended) := by
  intro hcode
  have kentry := keepsNonceOrCode_entered hentry
  obtain ⟨⟨hframe, hc⟩, hmeter, hpays⟩ := hrun (fun hs => kentry.2 _ (hcode hs)) rfl
  -- The call keeps each nonce or code and the block, as every call does.
  have kcall := keepsNonceOrCodeCall_rollbackOnError (meter := meter) hentry hframe
  have cplain : CreatesPlain state ended.state :=
    CreatesPlain.trans kentry (createsPlain_of_eq (createdAccounts_entered hentry)) hc
  have hpar' : ended.state.parent = state.parent :=
    hframe.1.2.trans (parent_entered hentry)
  have hkept : MeterKept meter (rollbackOnError state ended).gas :=
    meterRules_kept.trans hmeter (meterRules_kept.rollbackOnError state ended)
  -- The rest depends on whether the frame failed.
  have hend : ((rollbackOnError state ended).error ≠ none →
        (rollbackOnError state ended).gas.stateGasUsed = meter.restore.stateGasUsed) ∧
      min meter.stateGasUsed meter.restore.stateGasUsed +
          GasCosts.STORAGE_SET_STATE_GAS *
            (((nonceOrCodeFreshSlots (rollbackOnError state ended).state).card : Int) -
              (nonceOrCodeFreshSlots state).card) ≤
        (rollbackOnError state ended).gas.stateGasUsed := by
    rcases hpays with hf | ⟨-, hok⟩
    · -- A failed frame rolls back its meter to the floor, and the call puts back the state.
      have hused : (rollbackOnError state ended).gas.stateGasUsed =
          meter.restore.stateGasUsed :=
        (stateGasUsed_rollbackOnError_of_failed hf).trans (stateGasUsed_restore_congr hmeter)
      -- The accounts that the message created had no nonce or code at its start.
      --
      -- So the slots it counts are those of the state it started from.
      have hcard : nonceOrCodeFreshSlots (rollbackOnError state ended).state =
          nonceOrCodeFreshSlots state := by
        unfold rollbackOnError
        simp only [Option.isSome_iff_ne_none.mpr hf.2.1, ↓reduceIte]
        exact nonceOrCodeFreshSlots_restoreTxState hpar' cplain.1 cplain.2
      refine ⟨fun _ => hused, ?_⟩
      rw [hcard, hused, Int.sub_self, Int.mul_zero, Int.add_zero]
      exact Int.min_le_right _ _
    · -- A frame that succeeds ends with a surplus at least that of its start.
      obtain ⟨herr, hle⟩ := hok rfl
      have hE : rollbackOnError state ended = ended := by
        unfold rollbackOnError
        simp [herr]
      rw [hE]
      refine ⟨fun h => absurd herr h, ?_⟩
      have hle' : meter.stateGasUsed - GasCosts.STORAGE_SET_STATE_GAS *
          ((nonceOrCodeFreshSlots entry).card : Int) ≤ slotSurplus ended := hle
      rw [nonceOrCodeFreshSlots_entered hentry] at hle'
      unfold slotSurplus at hle'
      have := Int.min_le_left meter.stateGasUsed meter.restore.stateGasUsed
      rw [Int.mul_sub]
      omega
  refine ⟨kcall, cplain.of_created (createdAccounts_rollbackOnError state ended).1, hkept.2.2,
    hend.1, ?_⟩
  exact ⟨hkept.1, hkept.2.1, hend.2⟩

/-- A charge of a deposit of code does not lower the net state gas. -/
private theorem stateGasUsed_le_chargeCodeDeposit {meter after : StateGasMeter} {size : Nat}
    (h : chargeCodeDeposit fork meter size = .ok after) :
    meter.stateGasUsed ≤ after.stateGasUsed := by
  unfold chargeCodeDeposit at h
  split at h
  · -- A charge of execution gas keeps the net state gas, and one of state gas raises it.
    obtain ⟨mid, h1, h2⟩ := Base.bind_ok_iff.mp h
    rw [StateGasMeter.stateGasUsed_chargeState h2, StateGasMeter.stateGasUsed_charge h1]
    omega
  · exact (StateGasMeter.stateGasUsed_charge h).ge

/-- The frame that ends a creation, after the deposit of code.

It may put back the state, with the meter of an init code that failed, or with a halted meter.

It may keep the state and the meter.

It may store the code, and then its net state gas does not drop. -/
private theorem depositCode_slots {snapshot : TransactionState}
    {evm after : Evm fork StateGasMeter} (h : depositCode fork snapshot evm = .ok after) :
    (after.state = evm.state.restoreTxState snapshot ∧
        (evm.error ≠ none ∧ after.gas = evm.gas ∨ after.gas = evm.gas.halt)) ∨
      (after.state = evm.state ∧ after.gas = evm.gas) ∨
      (evm.state.setCode fork evm.message.currentTarget evm.output = .ok after.state ∧
        evm.gas.stateGasUsed ≤ after.gas.stateGasUsed) := by
  unfold depositCode at h
  dsimp only at h
  split at h
  · rename_i hs
    cases h
    exact .inl ⟨rfl, .inl ⟨Option.isSome_iff_ne_none.mp hs, rfl⟩⟩
  split at h
  · cases h
    exact .inl ⟨rfl, .inr rfl⟩
  split at h
  · cases h
    exact .inl ⟨rfl, .inr rfl⟩
  split at h
  · cases h
    split
    · exact .inl ⟨rfl, .inr rfl⟩
    · exact .inr (.inl ⟨rfl, rfl⟩)
  rename_i hc
  split at h
  · cases h
    exact .inl ⟨rfl, .inr rfl⟩
  obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact .inr (.inr ⟨Base.mapError_ok_iff.mp hst, stateGasUsed_le_chargeCodeDeposit hc⟩)

/-- From Glamsterdam, a creation ends as it should, once its init code ends as a call does. -/
private theorem createPays_depositCode (hfork : .glamsterdam ≤ fork) {message : Message fork}
    {state prepared : TransactionState} {substate : Substate} {meter : StateGasMeter}
    {evm after : Evm fork StateGasMeter}
    (hp : prepareCreation fork state message.currentTarget = .ok prepared)
    (hm : CallPays message prepared substate meter evm)
    (hd : depositCode fork state evm = .ok after) :
    CreatePays message state substate meter after := by
  intro hnc
  -- The start of the creation gives the address a nonce.
  have hsd : Fork.spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  have hnonce : 1 ≤ (prepared.getAccount message.currentTarget).nonce := by
    unfold prepareCreation at hp
    simp only [hsd, ↓reduceIte] at hp
    rw [(TransactionState.getAccount_incrementNonce (Base.mapError_ok_iff.mp hp)).1]
    exact Nat.succ_le_of_lt (Nat.succ_pos _)
  obtain ⟨kcall, hc, hbase, herr, hgrant, hcomm, hfloor⟩ := hm (fun _ => .inl hnonce)
  -- The creation keeps each nonce or code and the block, as every creation does.
  have kcreate := keepsNonceOrCodeCreate_depositCode hsd hp kcall hd
  obtain ⟨⟨hk, hpar⟩, hmsg⟩ := kcall
  have kprep := keepsNonceOrCode_prepareCreation hp
  have cevm : CreatesPlain state evm.state :=
    CreatesPlain.trans kprep (createsPlain_prepareCreation hnc hp) hc
  have pevm : evm.state.parent = state.parent := hpar.trans (parent_prepareCreation hp)
  have hmeter := meterRules_kept.depositCode hd
  have hnonce_evm : 1 ≤ (evm.state.getAccount evm.message.currentTarget).nonce := by
    rw [hmsg]
    exact Nat.le_trans hnonce (hk.1 message.currentTarget)
  rw [nonceOrCodeFreshSlots_prepareCreation hnc hp] at hfloor
  rcases depositCode_slots hd with ⟨hs, hg⟩ | ⟨hs, hg⟩ | ⟨hs, hg⟩
  · -- A failed creation puts back the state, and its meter is rolled back.
    have hcard : nonceOrCodeFreshSlots after.state = nonceOrCodeFreshSlots state := by
      rw [hs]
      exact nonceOrCodeFreshSlots_restoreTxState pevm cevm.1 cevm.2
    have hused : after.gas.stateGasUsed = meter.restore.stateGasUsed := by
      rcases hg with ⟨he, hg⟩ | hg
      · rw [hg]
        exact herr he
      · rw [hg]
        simp only [StateGasMeter.halt, StateGasMeter.restore, StateGasMeter.stateGasUsed, hgrant,
          hcomm, hbase]
    refine ⟨⟨kcreate, ?_⟩, hmeter.1.trans hgrant, hmeter.2.1.trans hcomm, ?_⟩
    · rw [hs]
      exact cevm.of_created rfl
    · rw [hcard, hused, Int.sub_self, Int.mul_zero, Int.add_zero]
      exact Int.min_le_right _ _
  · -- The state and the meter of the init code stay.
    refine ⟨⟨kcreate, hs ▸ cevm⟩, ?_⟩
    unfold MessagePays
    rw [hs, hg]
    exact ⟨hgrant, hcomm, hfloor⟩
  · -- The code goes to the address, which keeps its nonce, and the deposit charges state gas.
    refine ⟨⟨kcreate, cevm.of_created (TransactionState.createdAccounts_setCode hs)⟩,
      hmeter.1.trans hgrant, hmeter.2.1.trans hcomm, ?_⟩
    rw [nonceOrCodeFreshSlots_setCode hnonce_evm hs]
    exact hfloor.trans hg

/-- From Glamsterdam, by induction on gas, every call and creation ends as it should. -/
private theorem pays_induction (hfork : .glamsterdam ≤ fork) (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate)
      (meter : StateGasMeter) (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        CallPays message state substate meter ended.val) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate)
      (meter : StateGasMeter) (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        CreatePays message state substate meter ended.val) :=
  -- The proof is by strong induction on the gas of the message, for calls and creations together.
  processMessage_frame_byKind
    (F := fun a b => FrameInv a → a.error = none → FrameRel a b)
    (Mcall := CallPays) (Mcreate := CreatePays)
    (fun runs _ h hinv _ =>
      rel_runFrame frameRel_refl frameRel_trans frameInv_keeps
        (fun evm error _ => frameRel_halt evm error)
        (fun hinv running h => frameRel_step hfork hinv running h)
        (fun caller message lt ended _ hran => runs caller message lt ended hran) hinv h)
    (fun _ _ _ _ herr => ⟨stepRules_state.sameContext ⟨rfl, rfl, rfl, rfl⟩,
      meterRules_kept.refl _, Or.inr ⟨fun hf => hf.2.1 herr, fun _ => ⟨herr, le_rfl⟩⟩⟩)
    (fun _ _ hrp _ herr => ⟨stepRules_state.static (staticStep_runPrecompile hrp),
      meterRules_kept.runPrecompile hrp, paysSlots_runPrecompile herr hrp⟩)
    (fun hentry hrun => callPays_rollbackOnError hentry hrun)
    (fun hp hm hd => createPays_depositCode hfork hp hm hd) n

/-- From Glamsterdam, a call pays for the slots it counts.

When it has code, its current account must have a nonce or code.

That holds whether or not it ends with an error. -/
theorem processMessage_messagePays (hfork : .glamsterdam ≤ fork) {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : StateGasMeter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (hcode : message.code.size ≠ 0 → HasNonceOrCode state message.currentTarget)
    (h : processMessage fork message state substate meter held = .ok ended) :
    -- Its net state gas is at least a floor plus the state gas of the slots it adds.
    --
    -- The floor is the least of the net state gas of its meter and that of its meter rolled back.
    MessagePays message state substate meter ended.val :=
  ((pays_induction hfork message.gas).1 message state substate meter held rfl ended h
    hcode).2.2.2.2

/-- From Glamsterdam, a creation pays for the slots it counts.

Its address must have no nonce or code.

That holds whether or not it ends with an error. -/
theorem processCreateMessage_messagePays (hfork : .glamsterdam ≤ fork) {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : StateGasMeter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (hcode : ¬HasNonceOrCode state message.currentTarget)
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    MessagePays message state substate meter ended.val :=
  ((pays_induction hfork message.gas).2 message state substate meter held rfl ended h hcode).2

end EthLib.Execution.Evm
