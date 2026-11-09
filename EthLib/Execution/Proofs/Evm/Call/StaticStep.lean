module

public import EthLib.Execution.Proofs.Evm.Call.Create
public import EthLib.Execution.Proofs.Evm.Call.Instructions
public import EthLib.Execution.Proofs.Evm.Instructions.Static

/-!
# Proofs: the steps of a frame that must not change the state

A step of such a frame keeps its message, its code and its state, up to the records of its reads.

That holds for the steps of the four kinds of call before their message runs.

A call sends a static message that runs the code of a callee.

The code of a callee comes from an account that holds code, also through a delegation.

A value that a call sends goes to its own sender, whose account holds code.

A creation never completes in such a frame.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256 toAddressMasked)
open EthLib.Execution.State (EMPTY_CODE_HASH)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The calls -/

omit [GasMeter Meter] in
/-- The pops of the operands of a call are a static step.

A call that sends no value pops none. -/
theorem staticStep_popCallOperands {kind : CallKind} {evm after : Evm fork Meter}
    {call : CallOperands} (h : popCallOperands kind evm = .ok (call, after)) :
    StaticStep evm after ∧ (kind.sendsValue = false → call.value = 0) := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨v, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e6⟩, h6, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e7⟩, h7, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have p3 : StaticStep e2 e3 ∧ (kind.sendsValue = false → v = 0) := by
    unfold popCallValue at h3
    split at h3
    · exact ⟨StaticStep.of_sameContext (popWord_sameContext h3), fun h => by simp_all⟩
    · cases h3
      exact ⟨StaticStep.refl _, fun _ => rfl⟩
  refine ⟨?_, p3.2⟩
  exact (((((((StaticStep.of_sameContext (popWord_sameContext h1)).trans
    (StaticStep.of_sameContext (popWord_sameContext h2))).trans p3.1).trans
    (StaticStep.of_sameContext (popWord_sameContext h4))).trans
    (StaticStep.of_sameContext (popWord_sameContext h5))).trans
    (StaticStep.of_sameContext (popWord_sameContext h6))).trans
    (StaticStep.of_sameContext (popWord_sameContext h7)))

/-- The access to a delegate is a static step. -/
theorem staticStep_accessDelegation {evm after : Evm fork Meter} {address : Address}
    {known : Nat} {callee : Callee} (h : accessDelegation evm address known = .ok (callee, after)) :
    StaticStep evm after := by
  obtain ⟨code, -, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (staticStep_accessAddress _ _).trans (staticStep_recordAccountRead _ _)
  · cases h
    exact StaticStep.refl _

/-- The payment of a call is a static step. -/
theorem staticStep_payCall {kind : CallKind} {call : CallOperands}
    {memoryCost extraGas newAccount subCall : Nat} {evm after : Evm fork Meter}
    (h : payCall kind call memoryCost extraGas newAccount evm = .ok (subCall, after)) :
    StaticStep evm after := by
  unfold payCall at h
  split at h
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact ((StaticStep.of_sameContext (chargeGas_sameContext h1)).trans
      (StaticStep.of_sameContext (chargeStateGas_sameContext h2))).trans
      (StaticStep.of_sameContext (chargeGas_sameContext h3))
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact StaticStep.of_sameContext (chargeGas_sameContext h1)

/-- No delegation indicator is empty, so the empty code delegates nowhere. -/
theorem delegatedAddress_empty : delegatedAddress ByteArray.empty = none := by
  simp [delegatedAddress, isValidDelegation, DELEGATION_SIZE]

/-- A callee that holds code comes from an account whose code hash is not the empty one.

That holds for an account with code, and for an account whose code is an indicator of a delegate.
-/
theorem accessDelegation_codeHash_ne {evm after : Evm fork Meter} {address : Address}
    {known : Nat} {callee : Callee}
    (h : accessDelegation evm address known = .ok (callee, after))
    (nonempty : callee.code.size ≠ 0) :
    (evm.state.getAccount address).codeHash ≠ EMPTY_CODE_HASH := by
  intro hh
  unfold accessDelegation at h
  obtain ⟨code, hc, h⟩ := Base.bind_ok_iff.mp h
  have hcode : code = ByteArray.empty := by
    unfold accountCode at hc
    rw [hh] at hc
    simp [State.TransactionState.getCode, Except.mapError] at hc
    exact hc.symm
  subst hcode
  dsimp only at h
  split at h
  · rename_i d hd
    simp [delegatedAddress_empty] at hd
  · cases h
    exact nonempty rfl

/-- A call that runs no message is a static step. -/
theorem staticStep_skipCall {evm after : Evm fork Meter} {gas reservoir : Nat}
    (h : skipCall evm gas reservoir = .ok after) : StaticStep evm after := by
  obtain ⟨stack, -, rfl⟩ := skipCall_eq_ok h
  exact ⟨StateKept.refl _, rfl, rfl, rfl, rfl⟩

/-- The caller that takes in a child has the state of the child. -/
theorem state_incorporateChild (caller child : Evm fork Meter) :
    (incorporateChild fork caller child).state = child.state := by
  unfold incorporateChild
  split <;> rfl

/-- The caller that takes in a child keeps its code. -/
theorem code_incorporateChild (caller child : Evm fork Meter) :
    (incorporateChild fork caller child).code = caller.code := by
  unfold incorporateChild
  split <;> rfl

/-- The caller that takes in a child keeps its message. -/
theorem message_incorporateChild (caller child : Evm fork Meter) :
    (incorporateChild fork caller child).message = caller.message := by
  unfold incorporateChild
  split <;> rfl

/-- A message whose code runs at an account that holds code, or whose code is empty. -/
def StaticCode (state : State.TransactionState) (message : Message fork) : Prop :=
  message.code.size ≠ 0 →
    (state.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH

/-- A message that a static frame may send, from the state `state`.

It is static, and runs code of a callee.

Its code runs at an account that holds code.

A value that it sends goes to its own sender, whose account holds code. -/
def StaticMessage (state : State.TransactionState) (message : Message fork) : Prop :=
  message.isStatic = true ∧ message.target.isSome = true ∧ StaticCode state message ∧
    (message.shouldTransferValue = true → message.value ≠ 0 →
      message.caller = message.currentTarget ∧
        (state.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH)

omit [GasMeter Meter] in
/-- A static step keeps every account. -/
theorem getAccount_of_staticStep {a b : Evm fork Meter} (h : StaticStep a b)
    (address : Address) : b.state.getAccount address = a.state.getAccount address := by
  have := (h.state address (by simp)).1
  simp [State.TransactionState.getAccount, this]

/-- A creation never completes in a static frame. -/
theorem createStep_ne_ok_of_isStatic {create2 : Bool} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (static : evm.message.isStatic = true) :
    createStep create2 evm ≠ .ok result := by
  intro h
  unfold createStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [hs, and_self, ↓reduceIte] at h
    cases h
  simp only [hs, ↓reduceIte] at h
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
  have m4 : e4.message = e3.message := by
    unfold popSalt at h4
    split at h4
    · obtain ⟨⟨_, _⟩, hp, h4⟩ := Base.bind_ok_iff.mp h4
      cases h4
      exact (popWord_sameContext hp).message
    · cases h4
      rfl
  have m5 : e5.message = evm.message :=
    (chargeGasAndMemory_sameContext h5).message.trans (m4.trans
      ((popWord_sameContext h3).message.trans ((popWord_sameContext h2).message.trans
        (popWord_sameContext h1).message)))
  unfold genericCreate at h
  split at h
  · cases h
  · split at h
    · cases h
    · rw [m5] at *
      simp [static] at *

/-- A frame that runs a static message.

The frame has the code of its message.

That code runs at an account that holds code, when it has code. -/
def StaticFrame (evm : Evm fork Meter) : Prop :=
  evm.message.isStatic = true ∧ evm.code = evm.message.code ∧ StaticCode evm.state evm.message

omit [GasMeter Meter] in
/-- A static step from a static frame ends in a static frame. -/
theorem StaticFrame.of_staticStep {a b : Evm fork Meter} (h : StaticStep a b)
    (f : StaticFrame a) : StaticFrame b := by
  obtain ⟨hs, hc, hh⟩ := f
  refine ⟨by rw [h.message]; exact hs, by rw [h.code, h.message]; exact hc, ?_⟩
  intro nonempty
  rw [h.message] at nonempty ⊢
  rw [getAccount_of_staticStep h]
  exact hh nonempty

end EthLib.Execution.Evm
