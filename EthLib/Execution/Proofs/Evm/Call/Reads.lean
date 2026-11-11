module

public import EthLib.Execution.Proofs.Evm.Call.Instructions
public import EthLib.Execution.Proofs.State.Tracker

/-!
# Proofs: the reads of call preparation

A call records its target, once its gas check passes, before resolving a delegation.

Resolving a delegation records only the delegate, once its gas check passes.

From Glamsterdam, a failed gas check on the delegate halts the frame with the target read alone.

Call preparation then reads the current account's balance before deciding whether to run a message.

[EIP-7928][bal] keeps both reads when the call then fails its balance or depth check.

[EIP-7928][halt] also keeps every accessed address when the frame then halts.

Call preparation changes no storage read.

Paying for the call changes no transaction state.

The results describe the next frame or the caller before its child runs.

[bal]: https://eips.ethereum.org/EIPS/eip-7928#eip-7702-delegation
[halt]: https://eips.ethereum.org/EIPS/eip-7928#edge-cases-normative
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- Resolving a delegation adds exactly its delegate's account read.

With no delegate, it keeps the transaction state. -/
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
    change (accessAddress evm delegate).2.state.recordAccountRead delegate = _
    rw [state_accessAddress]

omit [GasMeter Meter] in
/-- A failed read of an account's code aborts the whole execution. -/
theorem aborts_of_accountCode {evm : Evm fork Meter} {address : Address} {e : EvmError}
    (h : accountCode evm address = .error e) : e.aborts = true := by
  unfold accountCode at h
  revert h
  cases evm.state.getCode (evm.state.getAccount address).codeHash with
  | error x =>
    intro h
    cases h
    rfl
  | ok code =>
    intro h
    cases h

/-- Resolving a delegation halts its frame only on the delegate's gas check, from Glamsterdam.

Every other failure aborts the whole execution. -/
theorem accessDelegation_halt {evm : Evm fork Meter} {address : Address} {known : Nat}
    {e : EvmError} (h : accessDelegation evm address known = .error e) (keep : e.aborts = false) :
    fork ≥ .glamsterdam ∧ e = .outOfGas ∧
      ∃ delegate, (if fork ≥ .pectra then
        (accountCode evm address).toOption.bind delegatedAddress else none) = some delegate := by
  unfold accessDelegation at h
  rcases Base.bind_eq_error h with h | ⟨code, hcode, h⟩
  · rw [aborts_of_accountCode h] at keep
    cases keep
  simp only [hcode, Except.toOption, Option.bind_some]
  dsimp only at h
  cases hd : (if fork ≥ .pectra then delegatedAddress code else none) with
  | none =>
    simp only [hd] at h
    cases h
  | some delegate =>
    simp only [hd] at h
    rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
    · unfold checkGas at h
      split at h
      · rename_i glamsterdam
        cases h
        exact ⟨glamsterdam.1, rfl, delegate, rfl⟩
      · cases h
    · rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
      · rw [aborts_of_accountCode h] at keep
        cases keep
      · cases h

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
  obtain ⟨_, -, rfl⟩ := skipCall_eq_ok h
  rfl

/-- A call that has paid keeps the transaction state, whether it runs a message or not. -/
theorem state_genericCall {evm : Evm fork Meter} {message : Message fork}
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

/-- Finishing a call adds exactly the current account's read, before its balance and depth checks.
-/
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

private theorem keepReads_eq_ok_halt {α : Type} {evm : Evm fork Meter}
    {halted : Evm fork Meter → α} {rest : Except EvmError α} {result : α}
    (h : keepReads evm halted rest = .ok result) :
    rest = .ok result ∨
      ∃ e, rest = .error e ∧ e.aborts = false ∧ result = halted (exceptionalHalt evm e) := by
  unfold keepReads at h
  split at h
  · split at h
    · cases h
    · rename_i keep
      cases h
      exact .inr ⟨_, rfl, by simpa using keep, rfl⟩
  · cases h
    exact .inl rfl

private theorem aborts_of_keepReads {α : Type} {evm : Evm fork Meter}
    {halted : Evm fork Meter → α} {rest : Except EvmError α} {e : EvmError}
    (h : keepReads evm halted rest = .error e) : e.aborts = true := by
  unfold keepReads at h
  split at h
  · split at h
    · rename_i aborts
      cases h
      exact aborts
    · cases h
  · cases h

/-- A call records its target, a resolved delegate, and then the current account.

A halt before delegation finishes keeps the target read.

It happens only from Glamsterdam, when the delegate's gas check fails.

A halt after delegation keeps any delegate read too.

A child is sent only after the current account is read.
-/
theorem state_callStep {kind : CallKind} {evm popped : Evm fork Meter} {call : CallOperands}
    {result : StepResult fork Meter} (pop : popCallOperands kind evm = .ok (call, popped))
    (h : callStep kind evm = .ok result) :
    let resolved := if fork ≥ .pectra then
      (accountCode evm call.address).toOption.bind delegatedAddress else none
    let target := evm.state.recordAccountRead call.address
    let delegated := match (generalizing := false) resolved with
      | some delegate => target.recordAccountRead delegate
      | none => target
    match (generalizing := false) result with
    | .next after =>
      (fork ≥ .glamsterdam ∧ (∃ delegate, resolved = some delegate) ∧
        after.state = target ∧ after.error = some .outOfGas) ∨
      (after.state = delegated ∧ ∃ e, after.error = some e) ∨
      after.state = delegated.recordAccountRead evm.message.currentTarget
    | .child caller _ _ =>
      caller.state = delegated.recordAccountRead evm.message.currentTarget := by
  have pstate : popped.state = evm.state := by rw [popCallOperands_eq_ok pop]
  have pmessage : popped.message = evm.message := by rw [popCallOperands_eq_ok pop]
  have accessedState : (accessAddress popped call.address).2.state = evm.state :=
    (state_accessAddress _ _).trans pstate
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
  rcases keepReads_eq_ok_halt h with h | ⟨e, he, keep, rfl⟩
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
  · rcases Base.bind_eq_error (α := Callee × Evm fork Meter) (β := StepResult fork Meter) he with
      he | ⟨⟨_, _⟩, -, he⟩
    · obtain ⟨glamsterdam, outOfGas, delegate, hd⟩ := accessDelegation_halt he keep
      rw [readCode] at hd
      subst outOfGas
      exact .inl ⟨glamsterdam, ⟨delegate, hd⟩, readState, rfl⟩
    · dsimp only at he
      rw [aborts_of_keepReads he] at keep
      cases keep

end EthLib.Execution.Evm
