module

public import EthLib.Execution.Proofs.Evm.Call.Instructions
public import EthLib.Execution.Proofs.State.Tracker

/-!
# Proofs: the reads of call preparation

A call records its target before resolving a delegation.

Resolving a delegation records only the delegate, once its gas check passes.

[EIP-7928][bal] requires both reads to survive a later halt of the instruction.

Call preparation then reads the current account's balance before deciding whether to run a message.

It changes no storage read, and its payment changes no state.

The results describe the next frame or the caller before its child runs.

[bal]: https://eips.ethereum.org/EIPS/eip-7928#eip-7702-delegation
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- Resolving a delegation adds exactly its delegate's account read, or changes no state. -/
theorem state_accessDelegation {evm after : Evm fork Meter} {address : Address} {known : Nat}
    {callee : Callee} (h : accessDelegation evm address known = .ok (callee, after)) :
    after.state =
      match (generalizing := false) (if fork ≥ .pectra then
        (accountCode evm address).toOption.bind delegatedAddress else none) with
      | some delegate => evm.state.recordAccountRead delegate
      | none => evm.state := by
  unfold accessDelegation at h
  obtain ⟨code, hcode, h⟩ := Base.bind_ok_iff.mp h
  simp only [hcode, Except.toOption, Option.bind_some]
  dsimp only at h
  cases hd : (if fork ≥ .pectra then delegatedAddress code else none) with
  | none =>
    simp only [hd] at h ⊢
    cases h
    rfl
  | some delegate =>
    simp only [hd] at h ⊢
    obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    obtain ⟨_, same⟩ := accessAddress_snd evm delegate
    rw [same]
    rfl

/-- Paying for a call keeps the whole transaction state, including every read. -/
theorem state_payCall {kind : CallKind} {call : CallOperands}
    {memoryCost extraGas newAccount subCall : Nat} {evm after : Evm fork Meter}
    (h : payCall kind call memoryCost extraGas newAccount evm = .ok (subCall, after)) :
    after.state = evm.state := by
  unfold payCall at h
  split at h
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (chargeGas_sameContext h3).state.trans
      ((chargeStateGas_sameContext h2).state.trans (chargeGas_sameContext h1).state)
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (chargeGas_sameContext h1).state

private theorem state_skipCall {evm after : Evm fork Meter} {gas reservoir : Nat}
    (h : skipCall evm gas reservoir = .ok after) : after.state = evm.state := by
  obtain ⟨_, pushed, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (pushWord_sameContext pushed).state

private theorem state_genericCall {evm : Evm fork Meter} {message : Message fork}
    {newAccount : Nat} {outputStart outputSize : Base.U256} {result : StepResult fork Meter}
    (h : genericCall evm message newAccount outputStart outputSize = .ok result) :
    match (generalizing := false) result with
    | .next after | .child after _ _ => after.state = evm.state := by
  unfold genericCall at h
  dsimp only at h
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    have same := state_skipCall hs
    exact same
  · cases h
    rfl

/-- Finishing a call adds exactly the current account's read before its balance or depth check. -/
theorem state_finishCall {kind : CallKind} {call : CallOperands} {callee : Callee}
    {subCall newAccount expandBy : Nat} {evm : Evm fork Meter} {result : StepResult fork Meter}
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    match (generalizing := false) result with
    | .next after | .child after _ _ =>
      after.state = evm.state.recordAccountRead evm.message.currentTarget := by
  unfold finishCall at h
  split at h
  · cases h
  dsimp only at h
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    have same := state_skipCall hs
    exact same
  · exact state_genericCall h

/-- A call records its target, a resolved delegate, and then the current account.

A halt before delegation finishes keeps the target read.

A later halt keeps the delegate read too; a child is sent only after the current account is read.
-/
theorem state_callStep {kind : CallKind} {evm popped : Evm fork Meter} {call : CallOperands}
    {result : StepResult fork Meter} (pop : popCallOperands kind evm = .ok (call, popped))
    (h : callStep kind evm = .ok result) :
    let target := evm.state.recordAccountRead call.address
    let delegated := match (generalizing := false) (if fork ≥ .pectra then
      (accountCode evm call.address).toOption.bind delegatedAddress else none) with
      | some delegate => target.recordAccountRead delegate
      | none => target
    match (generalizing := false) result with
    | .next after =>
      (after.state = target ∧ ∃ e, after.error = some e) ∨
      (after.state = delegated ∧ ∃ e, after.error = some e) ∨
      after.state = delegated.recordAccountRead evm.message.currentTarget
    | .child caller _ _ =>
      caller.state = delegated.recordAccountRead evm.message.currentTarget := by
  have pstate : popped.state = evm.state := by rw [popCallOperands_eq_ok pop]
  have pmessage : popped.message = evm.message := by rw [popCallOperands_eq_ok pop]
  have accessedState : (accessAddress popped call.address).2.state = evm.state := by
    obtain ⟨_, same⟩ := accessAddress_snd popped call.address
    rw [same]
    exact pstate
  have accessedMessage : (accessAddress popped call.address).2.message = evm.message :=
    (accessAddress_message _ _).trans pmessage
  let read := recordAccountRead (accessAddress popped call.address).2 call.address
  have readState : read.state = evm.state.recordAccountRead call.address := by
    change ((accessAddress popped call.address).2.state.recordAccountRead call.address) = _
    rw [accessedState]
  have readMessage : read.message = evm.message := accessedMessage
  have readCode : accountCode read call.address = accountCode evm call.address := by
    simp only [accountCode, read, recordAccountRead,
      State.TransactionState.getAccount_recordAccountRead,
      State.TransactionState.getCode_recordAccountRead, accessedState]
  unfold callStep at h
  simp only [pop, bind, Except.bind] at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw] at h
    cases h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨⟨callee, resolved⟩, hd, h⟩ := Base.bind_ok_iff.mp h
    have resolvedState := state_accessDelegation hd
    change resolved.state = _ at resolvedState
    rw [readCode, readState] at resolvedState
    have resolvedMessage : resolved.message = evm.message :=
      (accessDelegation_message hd).trans readMessage
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨⟨subCall, paid⟩, hp, h⟩ := Base.bind_ok_iff.mp h
      have state := state_finishCall h
      have paidState := (state_payCall hp).trans resolvedState
      have paidMessage := (payCall_message hp).trans resolvedMessage
      cases result with
      | next after => exact .inr (.inr (by simpa only [paidState, paidMessage] using state))
      | child caller message resume =>
        simpa only [paidState, paidMessage] using state
    · exact .inr (.inl ⟨resolvedState, e, rfl⟩)
  · exact .inl ⟨readState, e, rfl⟩

end EthLib.Execution.Evm
