module

public import EthLib.Execution.Proofs.Evm.Call.SlotSurplusSteps

/-!
# Proofs: each step pays for the slots it counts, given what its messages pay

From Glamsterdam, a call or a creation charges the state gas of a new account when it makes one.

It passes its whole reservoir to its message, which raises its net state gas by that reservoir.

The message ends having paid for its slots, from a meter whose floor is zero.

Taking it back adds the net state gas of the message and lowers that of the caller by the reservoir.

A message that failed gives back the state gas of the new account, which it did not make.

So does a call that runs no message, and a creation at an address that collides.

The rise of the nonce of the creator keeps the counted slots, since the creator has a nonce or code.

So each step from a running frame pays for its slots, from Glamsterdam.

Its code must run at an account with a nonce or code.

Each message it sends must pay for its slots, and so must the frame that resumes.

Source: [EIP-8037][eip8037], the state gas of a new account and its refill.

[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork}

/-! ## The meter and the counted slots of the parts of a call -/

/-- The merge of a child adds its net state gas, less its grant and its committed spill. -/
private theorem stateGasUsed_absorb_net (caller child : StateGasMeter) (succeeded : Bool) :
    (StateGasMeter.absorb caller child succeeded).stateGasUsed =
      caller.stateGasUsed + child.stateGasUsed - child.grant - child.committed := by
  unfold StateGasMeter.absorb
  split
  · rw [StateGasMeter.stateGasUsed_repay]
    simp only [StateGasMeter.stateGasUsed]
    omega
  · simp only [StateGasMeter.stateGasUsed]
    omega

/-- A refill of state gas lowers the surplus by its amount. -/
private theorem slotSurplus_refillStateGas (evm : Evm fork StateGasMeter) (amount : Nat) :
    slotSurplus (refillStateGas evm amount) = slotSurplus evm - amount := by
  simp only [slotSurplus, refillStateGas]
  have := StateGasMeter.stateGasUsed_refill evm.gas amount
  simp only [GasMeter.refill] at this ⊢
  omega

/-- The calling frame of a call has its surplus raised by the reservoir it passes on. -/
private theorem slotSurplus_callerFrame (evm : Evm fork StateGasMeter) (expandBy : Nat) :
    slotSurplus (callerFrame evm expandBy) = slotSurplus evm + evm.gas.reservoir := by
  unfold slotSurplus callerFrame
  rw [nonceOrCodeFreshSlots_of_readsMore (staticStep_recordAccountRead _ _).tracker]
  simp only [recordAccountRead, GasMeter.drain, StateGasMeter.drain, StateGasMeter.stateGasUsed]
  omega

/-- A caller that takes in a child that paid for its slots loses at most the reservoir it passed.

The child must pay from a meter that starts with that reservoir.

The merged frame keeps the error of the caller. -/
private theorem slotSurplus_incorporateChild {message : Message fork} {substate : Substate}
    {caller child : Evm fork StateGasMeter} {gas reservoir : Nat}
    (paid : MessagePays message caller.state substate (StateGasMeter.start gas reservoir) child) :
    (incorporateChild fork caller child).error = caller.error ∧
      slotSurplus caller - reservoir ≤ slotSurplus (incorporateChild fork caller child) := by
  obtain ⟨hgrant, hcommitted, hle⟩ := paid
  rw [min_stateGasUsed_start] at hle
  have hgas : (incorporateChild fork caller child).gas =
      StateGasMeter.absorb caller.gas child.gas child.error.isNone := by
    unfold incorporateChild
    split <;> rfl
  have hstate : (incorporateChild fork caller child).state = child.state := by
    unfold incorporateChild
    split <;> rfl
  have herr : (incorporateChild fork caller child).error = caller.error := by
    unfold incorporateChild
    split <;> rfl
  refine ⟨herr, ?_⟩
  -- The merge adds the net state gas of the child, less the reservoir it started with.
  simp only [slotSurplus, hgas, hstate, stateGasUsed_absorb_net, hgrant, hcommitted]
  simp only [StateGasMeter.start] at hle ⊢
  rw [Int.mul_sub] at hle
  omega

/-- A caller that resumes after a call that paid for its slots loses at most two amounts.

They are the reservoir it passed on and the state gas of the new account it gets back. -/
private theorem resumeCall_slotSurplus {message : Message fork} {substate : Substate}
    {caller child after : Evm fork StateGasMeter} {gas reservoir newAccount : Nat}
    {outputStart outputSize : U256}
    (paid : MessagePays message caller.state substate (StateGasMeter.start gas reservoir) child)
    (h : resumeCall fork caller newAccount outputStart outputSize child = .ok after) :
    after.error = caller.error ∧
      slotSurplus caller - reservoir - newAccount ≤ slotSurplus after := by
  obtain ⟨herr, hle⟩ := slotSurplus_incorporateChild paid
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  split at h1
  · obtain ⟨herr', hle'⟩ := surplusKept_pushWord h1
    exact ⟨herr'.trans herr, by simp only [slotSurplus, advance] at hle hle' ⊢; omega⟩
  · obtain ⟨herr', hle'⟩ := surplusKept_pushWord h1
    have := slotSurplus_refillStateGas (incorporateChild fork caller child) newAccount
    exact ⟨herr'.trans herr, by simp only [slotSurplus, advance] at hle hle' this ⊢; omega⟩

/-- A creator that resumes after a creation that paid for its slots loses at most two amounts.

They are the reservoir it passed on and the state gas of the new account it gets back. -/
private theorem resumeCreate_slotSurplus {message : Message fork} {substate : Substate}
    {caller child after : Evm fork StateGasMeter} {gas reservoir newAccount : Nat}
    {address : Address}
    (paid : MessagePays message caller.state substate (StateGasMeter.start gas reservoir) child)
    (h : resumeCreate fork caller newAccount address child = .ok after) :
    after.error = caller.error ∧
      slotSurplus caller - reservoir - newAccount ≤ slotSurplus after := by
  obtain ⟨herr, hle⟩ := slotSurplus_incorporateChild paid
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  split at h1
  · obtain ⟨herr', hle'⟩ := surplusKept_pushWord h1
    exact ⟨herr'.trans herr, by simp only [slotSurplus, advance] at hle hle' ⊢; omega⟩
  · obtain ⟨herr', hle'⟩ := surplusKept_pushWord h1
    have := slotSurplus_refillStateGas (incorporateChild fork caller child) newAccount
    exact ⟨herr'.trans herr, by simp only [slotSurplus, advance] at hle hle' this ⊢; omega⟩

/-- A charge of state gas raises the surplus by its amount, and keeps the error. -/
private theorem slotSurplus_chargeStateGas {evm after : Evm fork StateGasMeter} {amount : Nat}
    (h : chargeStateGas evm amount = .ok after) :
    after.error = evm.error ∧ slotSurplus after = slotSurplus evm + amount := by
  obtain ⟨gas, hgas, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have hused := StateGasMeter.stateGasUsed_chargeState hgas
  refine ⟨rfl, ?_⟩
  simp only [slotSurplus, hused]
  omega

/-! ## The calls -/

/-- The pops of the operands of a call keep the surplus. -/
private theorem surplusKept_popCallOperands {kind : CallKind} {evm after : Evm fork StateGasMeter}
    {call : CallOperands} (h : popCallOperands kind evm = .ok (call, after)) :
    SurplusKept evm after := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e6⟩, h6, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e7⟩, h7, h⟩ := Base.bind_ok_iff.mp h
  cases h
  -- The value is popped only by CALL and CALLCODE.
  have p3 : SurplusKept e2 e3 := by
    unfold popCallValue at h3
    split at h3
    · exact surplusKept_popWord h3
    · cases h3
      exact surplusKept_refl _
  exact ((((((surplusKept_popWord h1).trans (surplusKept_popWord h2)).trans p3).trans
    (surplusKept_popWord h4)).trans (surplusKept_popWord h5)).trans (surplusKept_popWord h6)).trans
    (surplusKept_popWord h7)

/-- The access to a delegate keeps the surplus. -/
private theorem surplusKept_accessDelegation {evm after : Evm fork StateGasMeter}
    {address : Address} {known : Nat} {callee : Callee}
    (h : accessDelegation evm address known = .ok (callee, after)) : SurplusKept evm after := by
  obtain ⟨code, -, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (surplusKept_accessAddress _ _).trans (surplusKept_recordAccountRead _ _)
  · cases h
    exact surplusKept_refl _

/-- From Glamsterdam, the payment of a call raises the surplus by the state gas of a new account.

That state gas must be zero for any call other than CALL. -/
private theorem payCall_slotSurplus (hfork : .glamsterdam ≤ fork) {kind : CallKind}
    {call : CallOperands} {memoryCost extraGas newAccount subCall : Nat}
    {evm after : Evm fork StateGasMeter} (hnew : kind ≠ .call → newAccount = 0)
    (h : payCall kind call memoryCost extraGas newAccount evm = .ok (subCall, after)) :
    after.error = evm.error ∧ slotSurplus evm + newAccount ≤ slotSurplus after := by
  unfold payCall at h
  split at h
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    -- Two charges of execution gas, and between them the state gas of the new account.
    have k1 := surplusKept_chargeGas h1
    have k2 := slotSurplus_chargeStateGas h2
    have k3 := surplusKept_chargeGas h3
    exact ⟨k3.1.trans (k2.1.trans k1.1), by have := k1.2; have := k3.2; omega⟩
  · rename_i hcall
    obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    cases h
    -- Any call other than CALL pays no state gas.
    rw [hnew fun hk => hcall ⟨hfork, hk⟩]
    have k1 := surplusKept_chargeGas h1
    exact ⟨k1.1, by have := k1.2; omega⟩

/-- A call that runs no message lowers the surplus by the reservoir it gets back. -/
private theorem skipCall_slotSurplus {evm after : Evm fork StateGasMeter} {gas reservoir : Nat}
    (h : skipCall evm gas reservoir = .ok after) :
    after.error = evm.error ∧ slotSurplus evm - reservoir ≤ slotSurplus after := by
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  obtain ⟨herr, hle⟩ := surplusKept_pushWord h1
  refine ⟨herr, le_trans (le_of_eq ?_) hle⟩
  simp only [slotSurplus, GasMeter.credit, StateGasMeter.cancel, StateGasMeter.start,
    StateGasMeter.stateGasUsed]
  omega

/-- The end of a call pays for its slots from a running frame, given what its message pays.

The frame that it ends from must keep the error of the running frame.

Its surplus must be at least that of the running frame plus the state gas of the new account. -/
private theorem finishCall_paysSlots {kind : CallKind} {call : CallOperands} {callee : Callee}
    {subCall newAccount expandBy : Nat} {start evm : Evm fork StateGasMeter}
    {result : StepResult fork StateGasMeter} (running : start.running = true)
    (herr : evm.error = start.error) (hle : slotSurplus start + newAccount ≤ slotSurplus evm)
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    StepResult.Keeps PaysSlots (ChildRel MessagePays) start result := by
  unfold finishCall at h
  split at h
  · cases h
  dsimp only at h
  -- The calling frame passes on its reservoir, which raises its surplus by that reservoir.
  have hc := slotSurplus_callerFrame evm expandBy
  have hr := slotSurplus_refillStateGas (callerFrame evm expandBy) newAccount
  have hres : GasMeter.reservoir evm.gas = evm.gas.reservoir := rfl
  split at h
  · -- A frame that lacks the value gets back the reservoir and the state gas of the new account.
    obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    obtain ⟨e1, l1⟩ := skipCall_slotSurplus hs
    exact PaysSlots.of_le running (e1.trans herr) (by omega)
  unfold genericCall at h
  split at h
  · -- A frame at the greatest depth gets them back too.
    obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    obtain ⟨e1, l1⟩ := skipCall_slotSurplus hs
    exact PaysSlots.of_le running (e1.trans herr) (by simp only [callMessage] at l1; omega)
  · cases h
    refine ⟨PaysSlots.of_le running herr (by omega), fun child after hres hpays => ?_⟩
    -- The caller takes back the child, which paid for its slots from the reservoir passed on.
    obtain ⟨e1, l1⟩ := resumeCall_slotSurplus hpays hres
    exact PaysSlots.of_le running (e1.trans herr) (by simp only [callMessage] at l1; omega)

/-- From Glamsterdam, the step of a call pays for its slots, given what its message pays.

The frame must run. -/
private theorem callStep_paysSlots (hfork : .glamsterdam ≤ fork) {kind : CallKind}
    {evm : Evm fork StateGasMeter} {result : StepResult fork StateGasMeter}
    (running : evm.running = true) (h : callStep kind evm = .ok result) :
    StepResult.Keeps PaysSlots (ChildRel MessagePays) evm result := by
  unfold callStep at h
  obtain ⟨⟨call, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    cases h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha := surplusKept_accessAddress e1 call.address
  rw [hacc] at ha
  -- The pops, the access and the read of the address keep the surplus.
  have s3 : SurplusKept evm (recordAccountRead e2 call.address) :=
    ((surplusKept_popCallOperands h1).trans ha).trans (surplusKept_recordAccountRead _ _)
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨⟨callee, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
    -- So does the access to a delegate.
    have s4 := s3.trans (surplusKept_accessDelegation h4)
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨⟨subCall, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
      -- Only CALL pays the state gas of a new account.
      have hnew : kind ≠ .call → callNewAccountStateGas fork kind e4.state call = 0 :=
        fun hk => by simp [callNewAccountStateGas, hk]
      obtain ⟨err5, le5⟩ := payCall_slotSurplus hfork hnew h5
      exact finishCall_paysSlots running (err5.trans s4.1) (by have := s4.2; omega) h
    · exact paysSlots_exceptionalHalt _ _ _
  · exact paysSlots_exceptionalHalt _ _ _

/-! ## The creations -/

/-- From Glamsterdam, the launch of a creation pays for its slots, given what its message pays.

The frame it starts from must keep the error and the surplus of a running frame.

Its current account must have a nonce or code. -/
private theorem launchCreate_paysSlots {start evm : Evm fork StateGasMeter} {value : U256}
    {initCode : ByteArray} {salt : Option U256} {result : StepResult fork StateGasMeter}
    (running : start.running = true) (kept : SurplusKept start evm)
    (hcode : HasNonceOrCode evm.state evm.message.currentTarget)
    (h : launchCreate evm value initCode salt = .ok result) :
    StepResult.Keeps PaysSlots (ChildRel MessagePays) start result := by
  unfold launchCreate at h
  dsimp only at h
  -- The read of the sender keeps the surplus.
  have s1 := kept.trans (surplusKept_recordAccountRead
    { evm with returnData := .empty } evm.message.currentTarget)
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    obtain ⟨e1, l1⟩ := skipCall_slotSurplus hs
    exact PaysSlots.of_le running (e1.trans s1.1) (by have := s1.2; omega)
  obtain ⟨address, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, ha⟩ := accessAddress_snd
    (recordAccountRead { evm with returnData := .empty } evm.message.currentTarget) address
  set A := recordAccountRead (accessAddress (recordAccountRead { evm with returnData := .empty }
    evm.message.currentTarget) address).2 address with hA
  -- The access to the new address and its read keep the surplus.
  have s2 : SurplusKept start A := s1.trans ((surplusKept_accessAddress _ address).trans
    (surplusKept_recordAccountRead _ address))
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨state, hst, h⟩ := Base.bind_ok_iff.mp h
    -- The state gas of the new account raises the surplus, and the charge of gas keeps it.
    have k1 := slotSurplus_chargeStateGas h1
    have k2 := surplusKept_chargeGas h2
    -- The sender keeps its nonce or code through the reads and the charges.
    have hcode' : HasNonceOrCode e2.state evm.message.currentTarget := by
      rw [(chargeGas_sameContext h2).state, (chargeStateGas_sameContext h1).state, hA, ha]
      rw [HasNonceOrCode.congr (tx := evm.state)]
      · exact hcode
      · simp [recordAccountRead]
    -- The rise of its nonce keeps the counted slots.
    have hslots := nonceOrCodeFreshSlots_incrementNonce hcode' (Base.mapError_ok_iff.mp hst)
    have hstate : slotSurplus { e2 with state } = slotSurplus e2 := by
      simp only [slotSurplus, hslots]
    have base : slotSurplus start + createNewAccountStateGas fork A.state address ≤
        slotSurplus { e2 with state } := by
      have := s2.2
      have := k2.2
      omega
    have herr : ({ e2 with state } : Evm fork StateGasMeter).error = start.error :=
      k2.1.trans (k1.1.trans s2.1)
    split at h
    · cases h
      -- The creator passes on its reservoir, which raises its surplus by that reservoir.
      have hd : slotSurplus { e2 with state, gas := GasMeter.drain e2.gas } =
          slotSurplus { e2 with state } + e2.gas.reservoir := by
        simp only [slotSurplus, GasMeter.drain, StateGasMeter.drain, StateGasMeter.stateGasUsed]
        omega
      refine ⟨PaysSlots.of_le running herr (by omega), fun child after hres hpays => ?_⟩
      -- The creator takes back the child, which paid for its slots from the reservoir passed on.
      obtain ⟨e3, l3⟩ := resumeCreate_slotSurplus hpays hres
      dsimp only at l3
      exact PaysSlots.of_le running (e3.trans herr) (by
        have : GasMeter.reservoir e2.gas = e2.gas.reservoir := rfl
        omega)
    · obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
      cases h
      -- A collision gets back the state gas of the new account.
      have k3 := surplusKept_pushWord h3
      have := slotSurplus_refillStateGas { e2 with state } (createNewAccountStateGas fork A.state
        address)
      refine PaysSlots.of_le running (k3.1.trans herr)
        (le_trans ?_ k3.2 : slotSurplus start ≤ slotSurplus e3)
      omega
  · exact paysSlots_exceptionalHalt _ _ _

/-- From Glamsterdam, the step of a creation pays for its slots, given what its message pays.

The frame must run, and its current account must have a nonce or code. -/
private theorem createStep_paysSlots {create2 : Bool} {evm : Evm fork StateGasMeter}
    {result : StepResult fork StateGasMeter} (running : evm.running = true)
    (hcode : HasNonceOrCode evm.state evm.message.currentTarget)
    (h : createStep create2 evm = .ok result) :
    StepResult.Keeps PaysSlots (ChildRel MessagePays) evm result := by
  unfold createStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [hs, and_self, ↓reduceIte] at h
    cases h
  simp only [hs, ↓reduceIte] at h
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨salt, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
  -- The pop of the salt keeps the surplus and the context.
  have m4 : SurplusKept e3 e4 ∧ SameContext e3 e4 := by
    unfold popSalt at h4
    split at h4
    · obtain ⟨⟨_, e⟩, he, h4⟩ := Base.bind_ok_iff.mp h4
      cases h4
      exact ⟨surplusKept_popWord he, popWord_sameContext he⟩
    · cases h4
      exact ⟨surplusKept_refl _, SameContext.refl _⟩
  -- The pops and the charge keep the surplus, the state and the message.
  have k5 : SurplusKept evm e5 := ((((surplusKept_popWord h1).trans (surplusKept_popWord h2)).trans
    (surplusKept_popWord h3)).trans m4.1).trans (surplusKept_chargeGasAndMemory h5)
  have c5 : SameContext evm e5 := ((((popWord_sameContext h1).trans (popWord_sameContext h2)).trans
    (popWord_sameContext h3)).trans m4.2).trans (chargeGasAndMemory_sameContext h5)
  have hcode5 : HasNonceOrCode e5.state e5.message.currentTarget := by
    rw [c5.state, c5.message]
    exact hcode
  unfold genericCreate at h
  split at h
  · cases h
  split at h
  · cases h
  exact launchCreate_paysSlots running k5 hcode5 h

/-- From Glamsterdam, each call and creation pays for its slots, given what its messages pay.

The frame must run, and its current account must have a nonce or code.

The frame it sends from pays.

So does the frame that resumes, when the message pays for its slots. -/
theorem paysSlots_messageInstruction (hfork : .glamsterdam ≤ fork) {op : Op}
    {run : Evm fork StateGasMeter → Except EvmError (StepResult fork StateGasMeter)}
    {evm : Evm fork StateGasMeter} {result : StepResult fork StateGasMeter}
    (running : evm.running = true) (hcode : HasNonceOrCode evm.state evm.message.currentTarget)
    (hrun : messageInstruction fork op = some run) (h : run evm = .ok result) :
    StepResult.Keeps PaysSlots (ChildRel MessagePays) evm result := by
  unfold messageInstruction at hrun
  cases hc : callInstruction (Meter := StateGasMeter) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals first
      | (subst hc; exact callStep_paysSlots hfork running h)
      | (split at hc
         · simp only [Option.some.injEq] at hc
           subst hc
           exact callStep_paysSlots hfork running h
         · cases hc)
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun
    all_goals first
      | (subst hrun; exact createStep_paysSlots running hcode h)
      | (split at hrun
         · simp only [Option.some.injEq] at hrun
           subst hrun
           exact createStep_paysSlots running hcode h
         · cases hrun)

/-- From Glamsterdam, each step of a running frame pays for its slots, given what its messages pay.

When its code is not empty, its current account must have a nonce or code. -/
theorem paysSlots_step (hfork : .glamsterdam ≤ fork) {evm : Evm fork StateGasMeter}
    {result : StepResult fork StateGasMeter} (running : evm.running = true)
    (hcode : evm.code.size ≠ 0 → HasNonceOrCode evm.state evm.message.currentTarget)
    (h : step fork evm = .ok result) :
    StepResult.Keeps PaysSlots (ChildRel MessagePays) evm result := by
  unfold Evm.step at h
  split at h
  · rename_i within
    dsimp only at h
    split at h
    · cases h
    · rename_i op decoded
      split at h
      · -- An instruction that gives the next frame pays by its own rule.
        rename_i run hop
        obtain ⟨after, hr, rfl⟩ := Base.map_ok_iff.mp h
        exact paysSlots_instruction hfork running (hcode (by omega)) hop hr
      · split at h
        · -- A call or a creation pays, given what its message pays.
          rename_i run hcall
          exact paysSlots_messageInstruction hfork running (hcode (by omega)) hcall h
        · cases h
  · -- Past the end of the code, the frame stops, and keeps its meter and its error.
    obtain ⟨after, hr, rfl⟩ := Base.map_ok_iff.mp h
    cases hr
    exact PaysSlots.of_le running rfl le_rfl

end EthLib.Execution.Evm
