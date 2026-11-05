module

public import EthLib.Execution.Evm.Call
public import EthLib.Execution.Proofs.Evm.Call.MessageCall
public import EthLib.Execution.Proofs.Evm.Gas.StateGas
public import EthLib.Execution.Proofs.Evm.Machine.Memory
public import EthLib.Execution.Proofs.Evm.Step

/-!
# Proofs: `Evm.Call`

From Glamsterdam, sending value with a call costs 11300 execution gas.

A new account then costs no execution gas, and CALL pays 183600 state gas for it instead.

Only CALL with value to a dead account pays that state gas, and no call pays it before Glamsterdam.

A callee that fails gives the caller back that state gas, and so does a call that runs no message.

With the meter of EIP-8037, the caller then has the net state gas it had before the call.

That holds when the failed callee has rolled back, as every failed message does.

The caller's memory then holds the start of the output in its output range.

A call fails with an error that does not abort the run in three cases only, in this order:

- The stack holds fewer words than the call pops.
- From Glamsterdam, the call is CALL with value in a static frame.
- From Glamsterdam, the frame holds less gas than the price that the call knows before it reads.

A static CALL with value runs no message at any fork.

A call that lacks the value, or that the depth limit stops, runs no message and pushes 0.

It gets back the gas it would pass on.

A message that fails leaves the caller a rollback to its state from before the call.

That rollback keeps the reads of the callee.

The caller then pushes 0, and the output of the callee becomes its return data.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256 byteAt byteAt_eq_getD)
open EthLib.Execution.State (TransactionState)
open GasCosts

variable {fork : Fork} {Meter : Type}

/-! ## Prices -/

/-- The state gas of a new account is 120 bytes at 1530 gas each. -/
theorem newAccountStateGas_eq : NEW_ACCOUNT_STATE_GAS = 183600 := rfl

/-- From Glamsterdam, sending value with a call costs 11300. -/
theorem callValueCost_of_glamsterdam (h : fork ≥ .glamsterdam) {value : U256} (hv : value ≠ 0) :
    callValueCost fork value = 11300 := by
  simp only [callValueCost, hv, h, ite_false, ite_true]
  rfl

/-- From Glamsterdam, a new account costs a call no execution gas. -/
theorem callNewAccountCost_of_glamsterdam (h : fork ≥ .glamsterdam)
    (state : State.TransactionState) (to : Base.Address) (value : U256) :
    callNewAccountCost fork state to value = 0 := by
  simp only [callNewAccountCost, h, ite_true]

/-- Before Glamsterdam, no call pays state gas. -/
theorem callNewAccountStateGas_of_lt (h : fork < .glamsterdam) (kind : CallKind)
    (state : State.TransactionState) (call : CallOperands) :
    callNewAccountStateGas fork kind state call = 0 := by
  have : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt h
  simp only [callNewAccountStateGas, this, false_and, ite_false]

/-- From Glamsterdam, a call pays state gas exactly when it is CALL with value to a dead account.

It then pays the state gas of a new account. -/
theorem callNewAccountStateGas_of_glamsterdam (h : fork ≥ .glamsterdam) (kind : CallKind)
    (state : State.TransactionState) (call : CallOperands) :
    callNewAccountStateGas fork kind state call =
      if kind = .call ∧ call.value ≠ 0 ∧ ¬state.isAccountAlive call.address then
        NEW_ACCOUNT_STATE_GAS
      else 0 := by
  simp only [callNewAccountStateGas, h, true_and]

/-! ## The refill -/

/-- A callee that fails gives the caller back `newAccount` state gas, after its own gas. -/
theorem resumeCall_gas_of_error [GasMeter Meter] {caller child after : Evm fork Meter}
    {newAccount : Nat} {outputStart outputSize : U256} (failed : child.error.isSome)
    (h : resumeCall fork caller newAccount outputStart outputSize child = .ok after) :
    after.gas = GasMeter.refill (GasMeter.absorb caller.gas child.gas false) newAccount := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  obtain ⟨_, -, h1⟩ := Base.bind_ok_iff.mp h1
  cases h1
  have hn : child.error.isNone = false := by
    cases e : child.error <;> simp_all
  simp only [advance, hn, Bool.false_eq_true, ite_false, refillStateGas, incorporateChild]

/-- A callee that succeeds gives the caller back its gas, and no state gas. -/
theorem resumeCall_gas_of_success [GasMeter Meter] {caller child after : Evm fork Meter}
    {newAccount : Nat} {outputStart outputSize : U256} (ok : child.error = none)
    (h : resumeCall fork caller newAccount outputStart outputSize child = .ok after) :
    after.gas = GasMeter.absorb caller.gas child.gas true := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  obtain ⟨_, -, h1⟩ := Base.bind_ok_iff.mp h1
  cases h1
  simp only [advance, ok, Option.isNone_none, ite_true, incorporateChild]

/-- A call that lacks the value runs no message.

The caller gets back `newAccount` state gas, then the gas and the reservoir of the message. -/
theorem finishCall_of_balance_lt [GasMeter Meter] {kind : CallKind} {call : CallOperands}
    {callee : Callee} {subCall newAccount expandBy : Nat} {evm : Evm fork Meter}
    {result : StepResult fork Meter}
    (low : (evm.state.getAccount evm.message.currentTarget).balance < call.value)
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    ∃ after, result = .next after ∧
      after.gas = GasMeter.credit (GasMeter.refill (GasMeter.drain evm.gas) newAccount) subCall
        (GasMeter.reservoir evm.gas) := by
  unfold finishCall at h
  split at h
  · cases h
  · dsimp only at h
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by exact low))] at h
    cases hs : skipCall (refillStateGas (recordAccountRead
        { evm with memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
        evm.message.currentTarget) newAccount) subCall (GasMeter.reservoir evm.gas) with
    | error => simp [hs, Functor.map, Except.map] at h
    | ok after =>
      simp only [hs, Functor.map, Except.map, Except.ok.injEq] at h
      refine ⟨after, h.symm, ?_⟩
      obtain ⟨_, h1, h2⟩ := Base.bind_ok_iff.mp hs
      cases h2
      obtain ⟨_, -, h1⟩ := Base.bind_ok_iff.mp h1
      cases h1
      rfl

/-! ## The net state gas of a call, with the meter of EIP-8037 -/

namespace StateGasMeter

/-- A failed callee gives the caller back the net state gas it had before the call.

The caller `meter` charges `amount` state gas, pays `gas`, and passes on its reservoir.

The callee then fails, and rolls back to the reservoir it got, with no spill.

The caller absorbs it and refills `amount`. -/
theorem stateGasUsed_call_of_error {meter charged paid child : StateGasMeter} {amount gas : Nat}
    (hc : meter.chargeState amount = .ok charged) (hp : charged.charge gas = .ok paid)
    (reservoir : child.reservoir = paid.reservoir) (spill : child.spill = 0) :
    ((paid.drain.absorb child false).refill amount).stateGasUsed = meter.stateGasUsed := by
  have hu := stateGasUsed_chargeState hc
  unfold charge at hp
  split at hp
  · cases hp
  · cases hp
    dsimp only at reservoir
    rw [stateGasUsed_refill]
    simp only [absorb, drain, Bool.false_eq_true, ite_false, stateGasUsed] at hu ⊢
    omega

/-- A call that runs no message gives the caller back the net state gas it had before the call.

The caller `meter` charges `amount` state gas, pays `gas`, and passes on its reservoir.

It then refills `amount`, and gets back `subCall` execution gas and its reservoir. -/
theorem stateGasUsed_call_of_skip {meter charged paid : StateGasMeter} {amount gas subCall : Nat}
    (hc : meter.chargeState amount = .ok charged) (hp : charged.charge gas = .ok paid) :
    ((paid.drain.refill amount).cancel (start subCall paid.reservoir)).stateGasUsed =
      meter.stateGasUsed := by
  have hu := stateGasUsed_chargeState hc
  unfold charge at hp
  split at hp
  · cases hp
  · cases hp
    simp only [cancel, refill, drain, start, stateGasUsed] at hu ⊢
    omega

end StateGasMeter

/-! ## The output in memory -/

/-- The caller's memory after a call holds the start of the output of the child in its range.

The copy has the smaller of `outputSize` and the size of the output as its size.

The caller keeps every other byte.

The output range must fit in the caller's memory when `outputSize` is not zero. -/
theorem byteAt_resumeCall [GasMeter Meter] {caller child after : Evm fork Meter} {newAccount : Nat}
    {outputStart outputSize : U256}
    (fit : outputSize ≠ 0 → outputStart.toNat + outputSize.toNat ≤ caller.memory.size)
    (h : resumeCall fork caller newAccount outputStart outputSize child = .ok after) (i : Nat) :
    byteAt after.memory i =
      if outputStart.toNat ≤ i ∧
          i < outputStart.toNat + min outputSize.toNat child.output.size then
        byteAt child.output (i - outputStart.toNat)
      else byteAt caller.memory i := by
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  obtain ⟨_, -, h1⟩ := Base.bind_ok_iff.mp h1
  cases h1
  have hm : (incorporateChild fork caller child).memory = caller.memory := by
    unfold incorporateChild
    split <;> rfl
  have hm' : (if child.error.isNone then incorporateChild fork caller child
      else refillStateGas (incorporateChild fork caller child) newAccount).memory =
      caller.memory := by
    split <;> exact hm
  simp only [advance]
  rw [hm']
  have hsize : (child.output.extract 0 (min outputSize.toNat child.output.size)).size =
      min outputSize.toNat child.output.size := by
    simp only [ByteArray.size_extract]
    omega
  by_cases hz : min outputSize.toNat child.output.size = 0
  · have hw : memoryWrite caller.memory outputStart.toNat
        (child.output.extract 0 (min outputSize.toNat child.output.size)) = caller.memory := by
      unfold memoryWrite
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [hsize, hz]))]
    rw [hw, hz, ite_eq_right_iff.mpr (fun hc => absurd hc.2 (by omega))]
  · have hnz : outputSize ≠ 0 := by
      rintro rfl
      exact hz (by simp)
    have := fit hnz
    rw [byteAt_memoryWrite (by rw [hsize]; omega), hsize]
    split
    · rename_i hin
      simp only [byteAt_eq_getD, ByteArray.data_extract, Array.getD_eq_getD_getElem?,
        Array.getElem?_extract]
      simp
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    · rfl

section Failures

variable [GasMeter Meter]

/-! ## The failures of a call -/

omit [GasMeter Meter] in
/-- The pops of a call fail exactly on a stack that holds too few words, with an underflow.

CALL and CALLCODE pop 7 words, and DELEGATECALL and STATICCALL pop 6. -/
theorem popCallOperands_eq_error_iff {kind : CallKind} {evm : Evm fork Meter} {e : EvmError} :
    popCallOperands kind evm = .error e ↔
      evm.stack.val.length < (if kind.sendsValue then 7 else 6) ∧ e = .stackUnderflow := by
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  rcases l with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, l⟩⟩⟩⟩⟩⟩⟩ <;>
    cases kind <;>
    simp [popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
      Except.bind, pure, Except.pure, eq_comm]
  all_goals intros; omega

omit [GasMeter Meter] in
/-- The pops of a call change only the stack of the frame. -/
theorem popCallOperands_eq_ok {kind : CallKind} {evm after : Evm fork Meter}
    {call : CallOperands} (h : popCallOperands kind evm = .ok (call, after)) :
    after = { evm with stack := after.stack } := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e6⟩, h6, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e7⟩, h7, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have pw : ∀ {a b : Evm fork Meter} {x : U256}, popWord a = .ok (x, b) →
      b = { a with stack := b.stack } := by
    intro a b x hp
    obtain ⟨⟨y, st⟩, -, hp⟩ := Base.bind_ok_iff.mp hp
    cases hp
    rfl
  have p3 : e3 = { e2 with stack := e3.stack } := by
    unfold popCallValue at h3
    split at h3
    · exact pw h3
    · cases h3
      rfl
  rw [pw h7, pw h6, pw h5, pw h4, p3, pw h2, pw h1]

omit [GasMeter Meter] in
/-- Whether an access to an address is cold does not depend on the stack.

The access keeps the gas of the frame. -/
theorem accessAddress_of_stack (evm : Evm fork Meter) (stack : Stack) (address : Base.Address) :
    (accessAddress { evm with stack } address).1 = (accessAddress evm address).1 ∧
      (accessAddress { evm with stack } address).2.gas = evm.gas := by
  unfold accessAddress
  split <;> exact ⟨rfl, rfl⟩

omit [GasMeter Meter] in
/-- The access to an address keeps the message of the frame. -/
theorem accessAddress_message (evm : Evm fork Meter) (address : Base.Address) :
    (accessAddress evm address).2.message = evm.message := by
  unfold accessAddress
  split <;> rfl

/-- The rest of an instruction that keeps its reads fails only with an error that aborts the run.

That error is the error of the rest. -/
theorem keepReads_eq_error {α : Type} {evm : Evm fork Meter} {halted : Evm fork Meter → α}
    {rest : Except EvmError α} {e : EvmError} :
    keepReads evm halted rest = .error e ↔ rest = .error e ∧ e.aborts = true := by
  unfold keepReads
  split
  · split <;> simp_all <;> rintro rfl <;> assumption
  · simp

/-- The access to a delegate keeps the message of the frame. -/
theorem accessDelegation_message {evm after : Evm fork Meter} {address : Base.Address}
    {known : Nat} {callee : Callee} (h : accessDelegation evm address known = .ok (callee, after)) :
    after.message = evm.message := by
  obtain ⟨code, -, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact accessAddress_message _ _
  · cases h
    rfl

/-- The payment of a call keeps the message of the frame. -/
theorem payCall_message {kind : CallKind} {call : CallOperands}
    {memoryCost extraGas newAccount subCall : Nat} {evm after : Evm fork Meter}
    (h : payCall kind call memoryCost extraGas newAccount evm = .ok (subCall, after)) :
    after.message = evm.message := by
  unfold payCall at h
  split at h
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    obtain ⟨_, -, h2⟩ := Base.bind_ok_iff.mp h2
    cases h2
    exact (chargeGas_sameContext h3).message.trans (chargeGas_sameContext h1).message
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (chargeGas_sameContext h1).message

/-- A call fails with an error that does not abort the run in three cases only.

The cases come in the order of the code.

First, the stack holds fewer words than the call pops, and the error is an underflow.

Second, from Glamsterdam, the call is CALL with value in a static frame.

Third, from Glamsterdam, the frame holds less gas than the price that the call knows.

That price is the access to the address, the price of the value and the growth of memory.

Each later error that does not abort the run gives a halted frame, not an error. -/
theorem callStep_eq_error_iff {kind : CallKind} {evm : Evm fork Meter} {e : EvmError}
    (halts : e.aborts = false) :
    callStep kind evm = .error e ↔
      (evm.stack.val.length < (if kind.sendsValue then 7 else 6) ∧ e = .stackUnderflow) ∨
      ∃ call after, popCallOperands kind evm = .ok (call, after) ∧
        ((fork ≥ .glamsterdam ∧ kind = .call ∧ evm.message.isStatic ∧ call.value ≠ 0 ∧
            e = .writeInStaticContext) ∨
          (¬(kind = .call ∧ evm.message.isStatic ∧ call.value ≠ 0) ∧ fork ≥ .glamsterdam ∧
            GasMeter.gasLeft evm.gas <
              callBaseCost fork (accessAddress evm call.address).1 +
                callValueCost fork call.value +
                (extendMemory evm.memory.size
                  [(call.inputStart, call.inputSize), (call.outputStart, call.outputSize)]).cost ∧
            e = .outOfGas)) := by
  rcases hp : popCallOperands kind evm with e' | ⟨call, after⟩
  · have under := popCallOperands_eq_error_iff.mp hp
    unfold callStep
    simp only [hp, bind, Except.bind, Except.error.injEq, reduceCtorEq, false_and, exists_false,
      or_false]
    constructor
    · rintro rfl
      exact under
    · rintro ⟨-, rfl⟩
      exact under.2
  · have long : ¬evm.stack.val.length < (if kind.sendsValue then 7 else 6) := fun lt => by
      have := popCallOperands_eq_error_iff.mpr ⟨lt, rfl⟩
      rw [hp] at this
      cases this
    have key : ∀ P : CallOperands → Prop,
        (∃ c a, (.ok (call, after) : Except EvmError (CallOperands × Evm fork Meter)) =
          .ok (c, a) ∧ P c) ↔ P call := fun P => by
      constructor
      · rintro ⟨c, a, h, hc⟩
        cases h
        exact hc
      · exact fun hc => ⟨_, _, rfl, hc⟩
    rw [key, or_iff_right (fun h => long h.1)]
    obtain ⟨s, rfl⟩ : ∃ s, after = { evm with stack := s } := ⟨_, popCallOperands_eq_ok hp⟩
    unfold callStep
    simp only [hp, bind, Except.bind]
    obtain ⟨cold, gas⟩ := accessAddress_of_stack evm s call.address
    rw [cold]
    by_cases hs : fork ≥ .glamsterdam ∧ kind = .call ∧ evm.message.isStatic ∧ call.value ≠ 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hs)]
      rw [show (throw .writeInStaticContext : Except EvmError Unit) = .error .writeInStaticContext
        from rfl]
      dsimp only
      constructor
      · intro h
        cases h
        exact .inl ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, rfl⟩
      · rintro (⟨-, -, -, -, rfl⟩ | ⟨hn, -⟩)
        · rfl
        · exact absurd hs.2 hn
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hs)]
      by_cases hg : fork ≥ .glamsterdam ∧ GasMeter.gasLeft evm.gas <
          callBaseCost fork (accessAddress evm call.address).1 + callValueCost fork call.value +
            (extendMemory evm.memory.size
              [(call.inputStart, call.inputSize), (call.outputStart, call.outputSize)]).cost
      · rw [checkGas, gas, ite_eq_left_of_eq_true _ _ (eq_true hg),
          show (throw .outOfGas : Except EvmError Unit) = .error .outOfGas from rfl]
        dsimp only
        constructor
        · intro h
          cases h
          exact .inr ⟨fun h => hs ⟨hg.1, h⟩, hg.1, hg.2, rfl⟩
        · rintro (h | ⟨-, -, -, rfl⟩)
          · exact absurd ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩ hs
          · rfl
      · rw [checkGas, gas, ite_eq_right_of_eq_false _ _ (eq_false hg),
          show (pure () : Except EvmError Unit) = .ok () from rfl]
        dsimp only
        rw [keepReads_eq_error, halts]
        constructor
        · rintro ⟨-, h⟩
          cases h
        · rintro (h | ⟨-, h1, h2, -⟩)
          · exact absurd ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩ hs
          · exact absurd ⟨h1, h2⟩ hg

/-- A static CALL with value runs no message, at every fork.

Its step gives a halted frame, or it fails with an error. -/
theorem callStep_of_static_value {evm after : Evm fork Meter} {call : CallOperands}
    {result : StepResult fork Meter} (hp : popCallOperands .call evm = .ok (call, after))
    (static : evm.message.isStatic = true) (hv : call.value ≠ 0)
    (h : callStep .call evm = .ok result) :
    ∃ halted e, result = .next (exceptionalHalt halted e) := by
  obtain ⟨⟨call', e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  rw [hp] at h1
  cases h1
  have m1 : after.message = evm.message := by rw [popCallOperands_eq_ok hp]
  dsimp only at h
  split at h
  · cases h
  rcases hacc : accessAddress after call.address with ⟨cold, e2⟩
  have m2 : e2.message = evm.message := by
    have := accessAddress_message after call.address
    rw [hacc] at this
    exact this.trans m1
  rw [hacc] at h
  dsimp only at h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨⟨callee, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨⟨subCall, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
      have m4 : e4.message = evm.message :=
        (payCall_message h4).trans ((accessDelegation_message h3).trans m2)
      unfold finishCall at h
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, m4 ▸ static, hv⟩)] at h
      cases h
    · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

/-- From Glamsterdam, a static CALL with value fails right after its pops.

The error holds no frame, and `runFrame_of_step_eq_error` halts the frame from before the step.

So the halted frame has no read that the call made. -/
theorem callStep_of_static_value_of_glamsterdam {evm after : Evm fork Meter}
    {call : CallOperands} (glamsterdam : fork ≥ .glamsterdam)
    (hp : popCallOperands .call evm = .ok (call, after)) (static : evm.message.isStatic = true)
    (hv : call.value ≠ 0) : callStep .call evm = .error .writeInStaticContext :=
  (callStep_eq_error_iff rfl).mpr (.inr ⟨call, after, hp, .inl ⟨glamsterdam, rfl, static, hv, rfl⟩⟩)

/-! ## A call that runs no message -/

/-- A call that runs no message pushes 0, moves the program counter, and empties the return data.

It gets back `gas` and `reservoir`, and keeps memory, the state and the substate. -/
theorem skipCall_eq_ok {evm after : Evm fork Meter} {gas reservoir : Nat}
    (h : skipCall evm gas reservoir = .ok after) :
    ∃ stack : Stack, stack.val = 0 :: evm.stack.val ∧
      after = advance { evm with
        gas := GasMeter.credit evm.gas gas reservoir, returnData := .empty, stack } := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  obtain ⟨stack, hs, h1⟩ := Base.bind_ok_iff.mp h1
  cases h1
  exact ⟨stack, (Stack.push_eq_ok_iff.mp hs).2, rfl⟩

/-- A call that lacks the value, or that the depth limit stops, runs no message.

The frame then pushes 0, moves the program counter, and empties the return data.

It gets back `newAccount` state gas, then the gas it would pass on and its reservoir.

Its memory grows, its state records a read of the current account, and its substate stays. -/
theorem finishCall_of_skip {kind : CallKind} {call : CallOperands}
    {callee : Callee} {subCall newAccount expandBy : Nat} {evm : Evm fork Meter}
    {result : StepResult fork Meter}
    (skip : (evm.state.getAccount evm.message.currentTarget).balance < call.value ∨
      evm.message.depth + 1 > STACK_DEPTH_LIMIT)
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    ∃ after stack, result = .next after ∧ stack.val = 0 :: evm.stack.val ∧
      after = advance { evm with
        memory := memoryExtend evm.memory expandBy
        gas := GasMeter.credit (GasMeter.refill (GasMeter.drain evm.gas) newAccount) subCall
          (GasMeter.reservoir evm.gas)
        state := evm.state.recordAccountRead evm.message.currentTarget
        returnData := .empty
        stack } := by
  unfold finishCall at h
  split at h
  · cases h
  dsimp only at h
  have next : ∀ {x : Except EvmError (Evm fork Meter)}, (.next <$> x) = .ok result →
      ∃ after, x = .ok after ∧ result = .next after := by
    intro x hx
    cases x with
    | error => cases hx
    | ok after =>
      cases hx
      exact ⟨after, rfl, rfl⟩
  split at h
  · obtain ⟨after, hs, rfl⟩ := next h
    obtain ⟨stack, hst, rfl⟩ := skipCall_eq_ok hs
    exact ⟨_, stack, rfl, hst, rfl⟩
  · rename_i low
    have deep : evm.message.depth + 1 > STACK_DEPTH_LIMIT := skip.resolve_left low
    unfold genericCall at h
    dsimp only at h
    split at h
    · obtain ⟨after, hs, rfl⟩ := next h
      obtain ⟨stack, hst, rfl⟩ := skipCall_eq_ok hs
      exact ⟨_, stack, rfl, hst, rfl⟩
    · exact absurd deep ‹_›

/-! ## The caller after a callee that fails -/

/-- The caller after a callee that fails or reverts.

The caller pushes 0, moves the program counter, and gets back `newAccount` state gas.

It takes the state of the callee, and its substate changes only in the touched accounts.

The output of the callee becomes the return data, and its start fills the output range. -/
theorem resumeCall_of_error {caller child after : Evm fork Meter}
    {newAccount : Nat} {outputStart outputSize : U256} (failed : child.error.isSome)
    (h : resumeCall fork caller newAccount outputStart outputSize child = .ok after) :
    ∃ stack : Stack, stack.val = 0 :: caller.stack.val ∧
      after = advance { caller with
        gas := GasMeter.refill (GasMeter.absorb caller.gas child.gas false) newAccount
        state := child.state
        substate := { caller.substate with
          touchedAccounts := touchedOnError fork caller child }
        returnData := child.output
        stack
        memory := memoryWrite caller.memory outputStart.toNat
          (child.output.extract 0 (min outputSize.toNat child.output.size)) } := by
  have hn : child.error.isNone = false := by
    cases e : child.error <;> simp_all
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  obtain ⟨stack, hs, h1⟩ := Base.bind_ok_iff.mp h1
  cases h1
  simp only [hn, Bool.false_eq_true, ite_false] at hs ⊢
  have hst := (Stack.push_eq_ok_iff.mp hs).2
  simp only [incorporateChild, hn, Bool.false_eq_true, ite_false, refillStateGas] at hst
  refine ⟨stack, hst, ?_⟩
  simp only [incorporateChild, hn, Bool.false_eq_true, ite_false, refillStateGas]

/-- After a message that fails, the caller has the writes of its state before the call.

That state is a rollback to the state of the caller, with the reads of the callee. -/
theorem resumeCall_processMessage_of_error [LawfulGasMeter Meter] {message : Message fork}
    {substate : Substate} {caller child after : Evm fork Meter}
    {used : GasMeter.gasHeld child.gas ≤ message.gas}
    {newAccount : Nat} {outputStart outputSize : U256}
    (ran : processMessage fork message caller.state substate = .ok ⟨child, used⟩)
    (failed : child.error.isSome)
    (h : resumeCall fork caller newAccount outputStart outputSize child = .ok after) :
    ∃ ended : TransactionState, after.state = ended.restoreTxState caller.state ∧
      SameWrites after.state caller.state ∧
      after.state.accountReads = ended.accountReads ∧
      after.state.storageReads = ended.storageReads := by
  obtain ⟨ended, he⟩ := processMessage_state_of_error ran failed
  obtain ⟨stack, -, rfl⟩ := resumeCall_of_error failed h
  exact ⟨ended, he, he ▸ sameWrites_restoreTxState _ _, he ▸ rfl, he ▸ rfl⟩

end Failures

end EthLib.Execution.Evm
