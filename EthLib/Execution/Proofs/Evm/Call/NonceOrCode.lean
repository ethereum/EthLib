module

public import EthLib.Execution.Proofs.Evm.Call.NonceOrCodeWrites

/-!
# Proofs: every message from Spurious Dragon keeps each nonce or code

An account has a nonce or code when its nonce is positive or it holds code.

A step lowers no nonce, and changes the code of no account.

A step deletes an account only when it is empty, so the account had no nonce and no code.

So every step keeps a nonce or code wherever there is one.

From Spurious Dragon, a creation raises the nonce of its address to 1 before it deposits code there.

So the code it deposits, even empty code, leaves a nonce at the address.

Before Spurious Dragon, empty code deposited at an address with code and nonce 0 leaves neither.

So the theorems below start at Spurious Dragon.

A rollback restores the accounts of a snapshot, which kept a nonce or code wherever it had one.

So from Spurious Dragon, every call and creation keeps a nonce or code wherever there is one.

That holds whatever the state, and whether or not the message ends with an error.

The rebuild property of the state is not needed.

[EIP-161][eip161] starts the nonce of a new account at 1.

[eip161]: https://eips.ethereum.org/EIPS/eip-161#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## A step -/

/-- Each write of a step keeps each nonce or code, static frame or not. -/
theorem stepRules_keepsNonceOrCode :
    StepRules fork (fun a b : Evm fork Meter => KeepsNonceOrCode a.state b.state) where
  trans := KeepsNonceOrCode.trans
  static h := keepsNonceOrCode_of_getAccountOptional fun address =>
    (h.state address List.not_mem_nil).1
  sstore _ _ _ _ _ _ h := keepsNonceOrCode_of_getAccountOptional fun _ =>
    TransactionState.getAccountOptional_setStorage h
  tstore _ _ _ _ := keepsNonceOrCode_of_getAccountOptional fun _ => rfl
  log _ hs _ _ _ := by rw [hs]; exact .refl _
  selfdestruct _ _ h := by
    unfold finishSelfdestruct at h
    split at h
    · cases h
    · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
      cases h
      exact keepsNonceOrCode_selfdestructTransfer (Base.mapError_ok_iff.mp hst)
  incrementNonce _ _ _ _ h := keepsNonceOrCode_incrementNonce h
  incorporate h := by rw [state_incorporateChild]; exact h

/-! ## Messages -/

/-- From Spurious Dragon, a deposit of code keeps each nonce or code of the state before a creation.

The init code must run at the address of the creation.

It must keep each nonce or code and the block. -/
private theorem keepsNonceOrCode_depositCode_of_prepared (hfork : .spuriousDragon ≤ fork)
    {state prepared : TransactionState} {address : Address} {evm after : Evm fork Meter}
    (hp : prepareCreation fork state address = .ok prepared)
    (hk : KeepsNonceOrCode prepared evm.state) (hpar : evm.state.parent = prepared.parent)
    (htarget : evm.message.currentTarget = address)
    (hd : depositCode fork state evm = .ok after) : KeepsNonceOrCode state after.state := by
  have k0 := keepsNonceOrCode_prepareCreation hp
  -- From Spurious Dragon, the address of the creation has a positive nonce once prepared.
  have hnonce : 1 ≤ (prepared.getAccount address).nonce := by
    unfold prepareCreation at hp
    simp only [show fork ≥ .spuriousDragon from hfork, ↓reduceIte] at hp
    rw [(TransactionState.getAccount_incrementNonce (Base.mapError_ok_iff.mp hp)).1]
    exact Nat.succ_le_of_lt (Nat.succ_pos _)
  -- The frame keeps that nonce, so the deposit keeps each nonce or code of the state before.
  refine keepsNonceOrCode_depositCode (k0.trans hk) (hpar.trans (parent_prepareCreation hp)) ?_ hd
  rw [htarget]
  exact Nat.le_trans hnonce (hk.1 address)

/-- A frame that keeps each nonce or code and the block, with its message and code. -/
private abbrev KeepsFrame (a b : Evm fork Meter) : Prop :=
  (KeepsNonceOrCode a.state b.state ∧ b.state.parent = a.state.parent) ∧
    b.message = a.message ∧ b.code = a.code

/-- A call that keeps each nonce or code and the block, and ends with its own message. -/
private abbrev KeepsCall (message : Message fork) (state : TransactionState) (_ : Substate)
    (_ : Meter) (ended : Evm fork Meter) : Prop :=
  (KeepsNonceOrCode state ended.state ∧ ended.state.parent = state.parent) ∧
    ended.message = message

/-- A creation that keeps each nonce or code and the block. -/
private abbrev KeepsCreate (_ : Message fork) (state : TransactionState) (_ : Substate)
    (_ : Meter) (ended : Evm fork Meter) : Prop :=
  KeepsNonceOrCode state ended.state ∧ ended.state.parent = state.parent

/-- A child, a call or a creation, keeps each nonce or code and the block of its caller. -/
private theorem keeps_of_childRelByKind {caller child : Evm fork Meter} {message : Message fork}
    (h : ChildRelByKind (Meter := Meter) KeepsCall KeepsCreate caller message child) :
    KeepsNonceOrCode caller.state child.state ∧ child.state.parent = caller.state.parent := by
  unfold ChildRelByKind ChildRel at h
  split at h
  · exact h.1
  · exact h

/-- A frame that resumes after a message keeps each nonce or code and the block of the frame before.

It also keeps its message and its code. -/
private theorem keepsFrame_resume {evm caller child after : Evm fork Meter}
    {message : Message fork} {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : step fork evm = .ok (.child caller message resume)) (resumed : resume child = .ok after)
    (hcaller : KeepsFrame evm caller)
    (hchild : ChildRelByKind (Meter := Meter) KeepsCall KeepsCreate caller message child) :
    KeepsFrame evm after := by
  have same := sameContext_of_step_eq_child h resumed
  obtain ⟨hk, hp⟩ := keeps_of_childRelByKind hchild
  -- The frame that resumes has the state of the child, and the message and code of the caller.
  have hs : after.state = child.state :=
    same.state.trans (state_incorporateChild caller child)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hs]
    exact hcaller.1.1.trans hk
  · rw [hs]
    exact hp.trans hcaller.1.2
  · rw [same.message, message_incorporateChild]
    exact hcaller.2.1
  · rw [same.code, code_incorporateChild]
    exact hcaller.2.2

/-- From Spurious Dragon, every call and creation keeps each nonce or code.

That holds whether or not the message ends with an error.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
theorem processMessage_keepsNonceOrCode_induction [LawfulGasMeter Meter]
    (hfork : .spuriousDragon ≤ fork) (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        KeepsNonceOrCode state ended.val.state) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        KeepsNonceOrCode state ended.val.state) := by
  have T := ((stepRules_keepsNonceOrCode (fork := fork) (Meter := Meter)).and
    stepRules_parent).and stepRules_messageCode
  -- Each step keeps the relation, a message it sends included.
  have steps : ∀ {evm : Evm fork Meter} {result : StepResult fork Meter}, True →
      step fork evm = .ok result →
      StepResult.Keeps KeepsFrame (ChildRelByKind KeepsCall KeepsCreate) evm result := by
    intro evm result _ h
    have r := T.step h
    cases result with
    | next after => exact r
    | child caller message resume =>
      exact ⟨r.1, fun child after hres hc => keepsFrame_resume h hres r.1 hc⟩
  have both := processMessage_rel_byKind (fork := fork) (Meter := Meter)
    (R := KeepsFrame) (Inv := fun _ => True) (Mcall := KeepsCall) (Mcreate := KeepsCreate)
    T.refl T.trans (fun _ _ => trivial)
    (fun evm error _ => T.static (staticStep_exceptionalHalt evm error))
    steps
    (fun _ _ => T.sameContext ⟨rfl, rfl, rfl, rfl⟩)
    (fun h _ => T.static (staticStep_runPrecompile h))
    (fun {_ state _ _ _ _ ended} hentry hrun =>
      ⟨⟨keepsNonceOrCode_rollbackOnError ((keepsNonceOrCode_entered hentry).trans
          (hrun trivial).1.1) ((hrun trivial).1.2.trans (parent_entered hentry)),
        (parent_rollbackOnError state ended).trans
          ((hrun trivial).1.2.trans (parent_entered hentry))⟩,
        (message_rollbackOnError state ended).trans (hrun trivial).2.1⟩)
    (fun hp hm hd => ⟨keepsNonceOrCode_depositCode_of_prepared hfork hp hm.1.1 hm.1.2
        (congrArg (·.currentTarget) hm.2) hd,
      (parent_depositCode hd).trans (hm.1.2.trans (parent_prepareCreation hp))⟩)
    n
  exact ⟨fun message state substate meter held hn ended h =>
      (both.1 message state substate meter held hn ended h).1.1,
    fun message state substate meter held hn ended h =>
      (both.2 message state substate meter held hn ended h).1⟩

/-- From Spurious Dragon, a call keeps each nonce or code.

It lowers no nonce, and keeps a nonce or code wherever there is one.

That holds whether or not it ends with an error. -/
theorem keepsNonceOrCode_processMessage [LawfulGasMeter Meter] (hfork : .spuriousDragon ≤ fork)
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended) :
    KeepsNonceOrCode state ended.val.state :=
  (processMessage_keepsNonceOrCode_induction hfork message.gas).1 message state substate meter
    held rfl ended h

/-- From Spurious Dragon, a creation keeps each nonce or code.

It lowers no nonce, and keeps a nonce or code wherever there is one.

That holds whether or not it ends with an error. -/
theorem keepsNonceOrCode_processCreateMessage [LawfulGasMeter Meter]
    (hfork : .spuriousDragon ≤ fork) {message : Message fork} {state : TransactionState}
    {substate : Substate} {meter : Meter} {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    KeepsNonceOrCode state ended.val.state :=
  (processMessage_keepsNonceOrCode_induction hfork message.gas).2 message state substate meter
    held rfl ended h

end EthLib.Execution.Evm
