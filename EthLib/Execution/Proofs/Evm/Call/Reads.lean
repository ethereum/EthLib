module

public import EthLib.Execution.Proofs.Evm.Call.Create
public import EthLib.Execution.Proofs.State.Tracker

/-!
# Proofs: the reads of call and creation preparation

A call records its target, once its gas check passes, before resolving a delegation.

Resolving a delegation records only the delegate, once its gas check passes.

From Glamsterdam, a failed gas check on the delegate halts the frame with the target read alone.

Call preparation then reads the current account's balance before deciding whether to run a message.

[EIP-7928][bal] keeps both reads when the call then fails its balance or depth check.

[EIP-7928][halt] also keeps every account read when the frame then halts.

Call preparation only adds account reads.

Paying for the call changes no transaction state.

A creation reads its sender before the checks on its balance, its nonce and the depth.

When one of those checks fails, it runs no message and keeps only the read of the sender.

Otherwise it reads the new address, and then either halts or raises the sender's nonce.

Both paths keep the reads of the sender and of the new address.

A creation also only adds account reads.

The results describe the next frame or the caller before its child runs.

[bal]: https://eips.ethereum.org/EIPS/eip-7928#eip-7702-delegation
[halt]: https://eips.ethereum.org/EIPS/eip-7928#edge-cases-normative
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The calls -/

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

/-- Resolving a delegation halts its frame only from Glamsterdam, when the frame lacks the gas.

That gas is the price known before and the price of the access to the delegate.

Every other failure aborts the whole execution. -/
theorem accessDelegation_halt {evm : Evm fork Meter} {address : Address} {known : Nat}
    {e : EvmError} (h : accessDelegation evm address known = .error e) (keep : e.aborts = false) :
    fork ≥ .glamsterdam ∧ e = .outOfGas ∧
      ∃ delegate, (if fork ≥ .pectra then
        (accountCode evm address).toOption.bind delegatedAddress else none) = some delegate ∧
        GasMeter.gasLeft (accessAddress evm delegate).2.gas <
          known + accountAccessCost fork (accessAddress evm delegate).1 := by
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
        exact ⟨glamsterdam.1, rfl, delegate, rfl, glamsterdam.2⟩
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

/-- A call records its target, a resolved delegate, and then the current account.

A halt before delegation finishes keeps the target read.

It happens only from Glamsterdam, with a resolved delegate, and the error is out of gas.

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
      (after.state = delegated ∧ ∃ e, e.aborts = false ∧ after.error = some e) ∨
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
    rcases keepReads_eq_ok_halt h with h | ⟨e, -, keep, rfl⟩
    · obtain ⟨⟨subCall, paid⟩, hp, h⟩ := Base.bind_ok_iff.mp h
      have state := state_finishCall h
      have paidState := (state_payCall hp).trans resolvedState
      have paidMessage := (payCall_message hp).trans resolvedMessage
      cases result with
      | next after => exact .inr (.inr (by simpa only [paidState, paidMessage] using state))
      | child caller message resume =>
        simpa only [paidState, paidMessage] using state
    · exact .inr (.inl ⟨resolvedState, e, keep, rfl⟩)
  · rcases Base.bind_eq_error (α := Callee × Evm fork Meter) (β := StepResult fork Meter) he with
      he | ⟨⟨_, _⟩, -, he⟩
    · obtain ⟨glamsterdam, outOfGas, delegate, hd, -⟩ := accessDelegation_halt he keep
      rw [readCode] at hd
      subst outOfGas
      exact .inl ⟨glamsterdam, ⟨delegate, hd⟩, readState, rfl⟩
    · dsimp only at he
      rw [(keepReads_eq_error.mp he).2] at keep
      cases keep

/-! ## The creations -/

/-- A creation that has paid reads its sender first, before the checks on the sender and the depth.

When one of those checks fails, it runs no message and keeps only the read of the sender.

Otherwise it derives the new address, reads it, then halts or raises the sender's nonce.

A halt keeps both reads, with an error that does not abort the execution.

At an address that is not deployable, it runs no message, and keeps both reads and the new nonce.

At a deployable address, it sends a message, and the caller keeps both reads and the new nonce. -/
theorem state_launchCreate {evm : Evm fork Meter} {value : U256} {initCode : ByteArray}
    {salt : Option U256} {result : StepResult fork Meter}
    (h : launchCreate evm value initCode salt = .ok result) :
    let current := evm.message.currentTarget
    let sender := evm.state.getAccount current
    let senderRead := evm.state.recordAccountRead current
    ((sender.balance < value ∨ sender.nonce = MAX_NONCE ∨
        evm.message.depth + 1 > STACK_DEPTH_LIMIT) ∧
      ∃ after, result = .next after ∧ after.state = senderRead) ∨
    (value ≤ sender.balance ∧ sender.nonce ≠ MAX_NONCE ∧
      evm.message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
      ∃ address, creationAddress current sender.nonce salt initCode = .ok address ∧
        let both := senderRead.recordAccountRead address
        match (generalizing := false) result with
        | .next after =>
          (after.state = both ∧ ∃ e, e.aborts = false ∧ after.error = some e) ∨
          (evm.state.accountDeployable address = false ∧
            both.incrementNonce fork current = .ok after.state)
        | .child caller _ _ =>
          evm.state.accountDeployable address = true ∧
            both.incrementNonce fork current = .ok caller.state) := by
  dsimp only
  by_cases fails : (evm.state.getAccount evm.message.currentTarget).balance < value ∨
      (evm.state.getAccount evm.message.currentTarget).nonce = MAX_NONCE ∨
      evm.message.depth + 1 > STACK_DEPTH_LIMIT
  · obtain ⟨after, rfl, hstate, -⟩ := launchCreate_of_preflight fails h
    exact .inl ⟨fails, after, rfl, hstate⟩
  · have hbal : value ≤ (evm.state.getAccount evm.message.currentTarget).balance :=
      BitVec.not_lt.mp fun hlt => fails (.inl hlt)
    have hnonce : (evm.state.getAccount evm.message.currentTarget).nonce ≠ MAX_NONCE :=
      fun hn => fails (.inr (.inl hn))
    have hdepth : evm.message.depth + 1 ≤ STACK_DEPTH_LIMIT :=
      Nat.not_lt.mp fun hd => fails (.inr (.inr hd))
    unfold launchCreate at h
    dsimp only at h
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by exact fails))] at h
    obtain ⟨address, haddr, h⟩ := Base.bind_ok_iff.mp h
    let read := recordAccountRead (accessAddress
      (recordAccountRead { evm with returnData := .empty } evm.message.currentTarget) address).2
      address
    have readState : read.state =
        (evm.state.recordAccountRead evm.message.currentTarget).recordAccountRead address := by
      change (accessAddress _ _).2.state.recordAccountRead address = _
      rw [state_accessAddress]
      rfl
    rcases keepReads_eq_ok_halt h with hr | ⟨e, -, keep, rfl⟩
    · obtain ⟨e1, h1, hr⟩ := Base.bind_ok_iff.mp hr
      obtain ⟨e2, h2, hr⟩ := Base.bind_ok_iff.mp hr
      obtain ⟨state, hinc, hr⟩ := Base.bind_ok_iff.mp hr
      have s2 : e2.state =
          (evm.state.recordAccountRead evm.message.currentTarget).recordAccountRead address :=
        (chargeGas_sameContext h2).state.trans
          ((chargeStateGas_sameContext h1).state.trans readState)
      have hinc' :
          ((evm.state.recordAccountRead evm.message.currentTarget).recordAccountRead
            address).incrementNonce fork evm.message.currentTarget = .ok state :=
        s2 ▸ Base.mapError_ok_iff.mp hinc
      have hdep : e2.state.accountDeployable address = evm.state.accountDeployable address := by
        rw [s2]
        rfl
      split at hr
      · rename_i dep
        cases hr
        exact .inr ⟨hbal, hnonce, hdepth, address, haddr, hdep ▸ dep, hinc'⟩
      · rename_i ndep
        obtain ⟨e3, h3, hr⟩ := Base.bind_ok_iff.mp hr
        cases hr
        have hdepFalse : evm.state.accountDeployable address = false :=
          Bool.eq_false_iff.mpr (hdep ▸ ndep)
        have s3 : (advance e3).state = state := (pushWord_sameContext h3).state
        exact .inr ⟨hbal, hnonce, hdepth, address, haddr, .inr ⟨hdepFalse, s3 ▸ hinc'⟩⟩
    · exact .inr ⟨hbal, hnonce, hdepth, address, haddr, .inl ⟨readState, e, keep, rfl⟩⟩

private theorem reads_incrementNonce_recordAccountRead {tx state : State.TransactionState}
    {current address : Address}
    (h : ((tx.recordAccountRead current).recordAccountRead address).incrementNonce
      fork current = .ok state) :
    state.accountReads = (tx.accountReads.insert current).insert address ∧
      state.storageReads = tx.storageReads := by
  obtain ⟨ha, hs⟩ := State.TransactionState.reads_incrementNonce h
  refine ⟨?_, hs⟩
  rw [ha]
  ext a
  simp [State.TransactionState.recordAccountRead, Std.ExtTreeSet.mem_insert, or_left_comm]

/-- A creation that has paid adds its sender to the account reads, and keeps the storage reads.

When the checks on the sender and the depth pass, it also adds the new address.

That holds whether the step then halts, finds a collision at the new address, or sends a message. -/
theorem reads_launchCreate {evm : Evm fork Meter} {value : U256} {initCode : ByteArray}
    {salt : Option U256} {result : StepResult fork Meter}
    (h : launchCreate evm value initCode salt = .ok result) :
    let current := evm.message.currentTarget
    let sender := evm.state.getAccount current
    ((sender.balance < value ∨ sender.nonce = MAX_NONCE ∨
        evm.message.depth + 1 > STACK_DEPTH_LIMIT) ∧
      ∃ after, result = .next after ∧
        after.state.accountReads = evm.state.accountReads.insert current ∧
        after.state.storageReads = evm.state.storageReads) ∨
    (value ≤ sender.balance ∧ sender.nonce ≠ MAX_NONCE ∧
      evm.message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
      ∃ address, creationAddress current sender.nonce salt initCode = .ok address ∧
        match (generalizing := false) result with
        | .next after | .child after _ _ =>
          after.state.accountReads = (evm.state.accountReads.insert current).insert address ∧
            after.state.storageReads = evm.state.storageReads) := by
  rcases state_launchCreate h with ⟨fails, after, rfl, hstate⟩ |
      ⟨hbal, hnonce, hdepth, address, haddr, hres⟩
  · exact .inl ⟨fails, after, rfl, by rw [hstate]; rfl, by rw [hstate]; rfl⟩
  · refine .inr ⟨hbal, hnonce, hdepth, address, haddr, ?_⟩
    cases result with
    | next after =>
      dsimp only
      rcases hres with ⟨hstate, -⟩ | ⟨-, hinc⟩
      · rw [hstate]
        exact ⟨rfl, rfl⟩
      · exact reads_incrementNonce_recordAccountRead hinc
    | child caller message resume =>
      dsimp only
      exact reads_incrementNonce_recordAccountRead hres.2

/-- CREATE and CREATE2 read the sender first, before the checks on the sender and the depth.

When one of those checks fails, they run no message and keep only the read of the sender.

Otherwise they derive the new address and read it.

CREATE2 hashes the init code that it reads from the grown memory.

A halt keeps both reads, with an error that does not abort the execution.

At an address that is not deployable, they run no message, and keep both reads and the new nonce.

At a deployable address, they send a message, and the caller keeps both reads and the new nonce. -/
theorem state_createStep {create2 : Bool} {evm : Evm fork Meter} {value start size : U256}
    {rest : List U256} {result : StepResult fork Meter}
    (hs : evm.stack.val = value :: start :: size :: rest)
    (h : createStep create2 evm = .ok result) :
    let current := evm.message.currentTarget
    let sender := evm.state.getAccount current
    let senderRead := evm.state.recordAccountRead current
    let initCode := memoryReadBytes
      (memoryExtend evm.memory (extendMemory evm.memory.size [(start, size)]).expandBy)
      start.toNat size.toNat
    let salt := if create2 then rest.head? else none
    ((sender.balance < value ∨ sender.nonce = MAX_NONCE ∨
        evm.message.depth + 1 > STACK_DEPTH_LIMIT) ∧
      ∃ after, result = .next after ∧ after.state = senderRead) ∨
    (value ≤ sender.balance ∧ sender.nonce ≠ MAX_NONCE ∧
      evm.message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
      ∃ address, creationAddress current sender.nonce salt initCode = .ok address ∧
        let both := senderRead.recordAccountRead address
        match (generalizing := false) result with
        | .next after =>
          (after.state = both ∧ ∃ e, e.aborts = false ∧ after.error = some e) ∨
          (evm.state.accountDeployable address = false ∧
            both.incrementNonce fork current = .ok after.state)
        | .child caller _ _ =>
          evm.state.accountDeployable address = true ∧
            both.incrementNonce fork current = .ok caller.state) := by
  obtain ⟨v, st, sz, r, paid, hstack, sc, hmem, -, -, hlaunch⟩ := createStep_eq_ok h
  obtain ⟨rfl, rfl, rfl, rfl⟩ : v = value ∧ st = start ∧ sz = size ∧ r = rest := by
    simpa using hstack.symm.trans hs
  have hstate := state_launchCreate hlaunch
  simpa only [sc.state, sc.message, hmem] using hstate

/-- CREATE and CREATE2 add the sender to the account reads, and keep the storage reads.

When the checks on the sender and the depth pass, they also add the new address.

That holds whether the step then halts, finds a collision at the new address, or sends a message. -/
theorem reads_createStep {create2 : Bool} {evm : Evm fork Meter} {value start size : U256}
    {rest : List U256} {result : StepResult fork Meter}
    (hs : evm.stack.val = value :: start :: size :: rest)
    (h : createStep create2 evm = .ok result) :
    let current := evm.message.currentTarget
    let sender := evm.state.getAccount current
    let initCode := memoryReadBytes
      (memoryExtend evm.memory (extendMemory evm.memory.size [(start, size)]).expandBy)
      start.toNat size.toNat
    let salt := if create2 then rest.head? else none
    ((sender.balance < value ∨ sender.nonce = MAX_NONCE ∨
        evm.message.depth + 1 > STACK_DEPTH_LIMIT) ∧
      ∃ after, result = .next after ∧
        after.state.accountReads = evm.state.accountReads.insert current ∧
        after.state.storageReads = evm.state.storageReads) ∨
    (value ≤ sender.balance ∧ sender.nonce ≠ MAX_NONCE ∧
      evm.message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
      ∃ address, creationAddress current sender.nonce salt initCode = .ok address ∧
        match (generalizing := false) result with
        | .next after | .child after _ _ =>
          after.state.accountReads = (evm.state.accountReads.insert current).insert address ∧
            after.state.storageReads = evm.state.storageReads) := by
  obtain ⟨v, st, sz, r, paid, hstack, sc, hmem, -, -, hlaunch⟩ := createStep_eq_ok h
  obtain ⟨rfl, rfl, rfl, rfl⟩ : v = value ∧ st = start ∧ sz = size ∧ r = rest := by
    simpa using hstack.symm.trans hs
  have hreads := reads_launchCreate hlaunch
  simpa only [sc.state, sc.message, hmem] using hreads

end EthLib.Execution.Evm
