module

public import EthLib.Execution.Evm.Gas.CallGas
public import EthLib.Execution.Evm.Call.Child
public import EthLib.Execution.Evm.Call.Delegation
public import EthLib.Execution.Evm.Measure

/-!
# `Evm.Call.Instructions`

The four instructions that call an account: CALL, CALLCODE, DELEGATECALL and STATICCALL.

A call pops its operands, pays, and grows memory for its input and its output.

It then runs a message, unless the depth limit or the balance of the frame forbids it.

A call that runs no message gets back the gas it would pass on, and pushes 0.

After the message, the caller gets back the gas left of the callee and keeps its output.

It pushes 1 when the callee succeeded, and copies the output to memory.

CALLCODE runs the code of another account on the current account, so it creates no account.

DELEGATECALL also keeps the sender and the value of the current message, and moves no value.

STATICCALL sends no value, and its callee must not change the state.

From Pectra, a callee whose code is a delegation indicator runs the code of its delegate.

The call then pays for the access to the delegate too.

From Glamsterdam, CALL with value to a dead account pays the state gas of a new account.

It pays its execution gas first, then that state gas, then the gas it passes on.

So state gas that spills into execution gas lowers the gas passed on.

The state gas comes back when the call runs no message, or when its callee fails.

CALL with value in a frame that must not change the state then fails right after its pops.

A callee gets less gas than the call pays, so each call lowers the measure of the frame.

Appendix H.2 of the Yellow Paper, Shanghai version, defines these instructions.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

The EIPs that add or change an instruction define it:

- [EIP-7][eip7], DELEGATECALL
- [EIP-211][eip211], the return data of a call
- [EIP-214][eip214], STATICCALL
- [EIP-2929][eip2929], the cold and warm accesses
- [EIP-7702][eip7702], the delegation indicator
- [EIP-8037][eip8037], the state gas of a new account, in Last Call

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip7]: https://eips.ethereum.org/EIPS/eip-7#specification
[eip211]: https://eips.ethereum.org/EIPS/eip-211#specification
[eip214]: https://eips.ethereum.org/EIPS/eip-214#specification
[eip2929]: https://eips.ethereum.org/EIPS/eip-2929#specification
[eip7702]: https://eips.ethereum.org/EIPS/eip-7702#delegation-indicator
[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#gas-accounting-for-new-accounts
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256 toAddressMasked)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The instructions -/

/-- The four instructions that call an account. -/
inductive CallKind where
  /-- CALL: run the code of an account on that account. -/
  | call
  /-- CALLCODE: run the code of an account on the current account. -/
  | callcode
  /-- DELEGATECALL: as CALLCODE, with the sender and the value of the current message. -/
  | delegatecall
  /-- STATICCALL: as CALL with no value, and the callee must not change the state. -/
  | staticcall
  deriving DecidableEq, Repr

/-- Whether the instruction pops a value to send: CALL and CALLCODE do. -/
def CallKind.sendsValue : CallKind → Bool
  | .call | .callcode => true
  | .delegatecall | .staticcall => false

/-- The code that a call runs, once it follows a delegation. -/
structure Callee where
  /-- The account whose code runs. -/
  codeAddress : Address
  /-- The code that runs. -/
  code : ByteArray
  /-- Whether the code is that of a delegate, so a precompile at its address does not run. -/
  delegated : Bool
  /-- The price of the access to the delegate, or 0 with no delegation. -/
  accessCost : Nat

/-- The code that a call to `address` runs, and the frame after the access to a delegate.

From Pectra, the code of a delegated account is a delegation indicator.

The call then runs the code of the delegate, and pays a cold or a warm access to it.

It follows one delegation only, even when the delegate has an indicator too.

From Glamsterdam, the frame must hold `known` gas and the access to the delegate first.

`known` is the price that the call knows before it reads the state.

Only then does it read the delegate, which EIP-7928 records.

Before Pectra, the call runs the code of the account at `address`. -/
def accessDelegation (evm : Evm fork Meter) (address : Address) (known : Nat) :
    Except EvmError (Callee × Evm fork Meter) := do
  let code ← accountCode evm address
  let delegate := if fork ≥ .pectra then delegatedAddress code else none
  match delegate with
  | some delegate =>
    let (cold, evm) := accessAddress evm delegate
    let cost := accountAccessCost fork cold
    checkGas evm (known + cost)
    let evm := recordAccountRead evm delegate
    let code ← accountCode evm delegate
    return (⟨delegate, code, true, cost⟩, evm)
  | none => return (⟨address, code, false, 0⟩, evm)

/-- The frame after a call that runs no message: it gets back `gas` and `reservoir`, and pushes 0.

The return data is empty. -/
def skipCall (evm : Evm fork Meter) (gas reservoir : Nat) : Except EvmError (Evm fork Meter) := do
  let evm ←
    pushWord { evm with gas := GasMeter.credit evm.gas gas reservoir, returnData := .empty } 0
  return advance evm

/-- The calling frame `caller` once its callee ends with the frame `child`.

It pushes 1 when the callee succeeded, and 0 when it failed or reverted.

A callee that failed creates no account, so the caller gets back `newAccount` state gas.

The output of the callee becomes the return data.

The start of that output fills the output range of memory, as far as either goes. -/
def resumeCall (fork : Fork) (caller : Evm fork Meter) (newAccount : Nat)
    (outputStart outputSize : U256) (child : Evm fork Meter) :
    Except EvmError (Evm fork Meter) := do
  let evm := incorporateChild fork caller child
  let evm := if child.error.isNone then evm else refillStateGas evm newAccount
  let evm := { evm with returnData := child.output }
  let evm ← pushWord evm (if child.error.isNone then 1 else 0)
  let output := child.output.extract 0 (min outputSize.toNat child.output.size)
  return advance { evm with memory := memoryWrite evm.memory outputStart.toNat output }

/-- The step of a call that has paid: run `message` first, unless the depth forbids it.

The call empties the return data.

A frame at the greatest depth runs no message.

It gets back the gas and the reservoir of the message, and the `newAccount` state gas it paid. -/
def genericCall (evm : Evm fork Meter) (message : Message fork) (newAccount : Nat)
    (outputStart outputSize : U256) : Except EvmError (StepResult fork Meter) :=
  let evm := { evm with returnData := .empty }
  if evm.message.depth + 1 > STACK_DEPTH_LIMIT then
    .next <$> skipCall (refillStateGas evm newAccount) message.gas message.reservoir
  else .ok (.child evm message (resumeCall fork evm newAccount outputStart outputSize))

/-- The operands of a call. -/
structure CallOperands where
  /-- The gas that the call asks to pass on. -/
  gas : U256
  /-- The account called, or whose code runs for CALLCODE and DELEGATECALL. -/
  address : Address
  /-- The value to send, which is 0 for DELEGATECALL and STATICCALL. -/
  value : U256
  /-- The start of the input in memory. -/
  inputStart : U256
  /-- The size of the input. -/
  inputSize : U256
  /-- The start of the output range in memory. -/
  outputStart : U256
  /-- The size of the output range. -/
  outputSize : U256

/-- The value that a call of kind `kind` pops: CALL and CALLCODE pop one, and others take 0. -/
def popCallValue (kind : CallKind) (evm : Evm fork Meter) :
    Except EvmError (U256 × Evm fork Meter) :=
  if kind.sendsValue then popWord evm else .ok (0, evm)

/-- The operands that a call of kind `kind` pops, and the frame after the pops.

The value comes third. -/
def popCallOperands (kind : CallKind) (evm : Evm fork Meter) :
    Except EvmError (CallOperands × Evm fork Meter) := do
  let (gas, evm) ← popWord evm
  let (address, evm) ← popWord evm
  let (value, evm) ← popCallValue kind evm
  let (inputStart, evm) ← popWord evm
  let (inputSize, evm) ← popWord evm
  let (outputStart, evm) ← popWord evm
  let (outputSize, evm) ← popWord evm
  return (⟨gas, toAddressMasked address, value, inputStart, inputSize, outputStart, outputSize⟩,
    evm)

/-- The extra price of a call at fork `fork`, on top of the gas it passes on.

It adds the access to the address, the access to a delegate, and the price of the value.

CALL to an account that the value would create pays for that account too. -/
def callExtraGas (fork : Fork) (kind : CallKind) (state : State.TransactionState)
    (call : CallOperands) (cold : Bool) (callee : Callee) : Nat :=
  let newAccountCost :=
    if kind = .call then callNewAccountCost fork state call.address call.value else 0
  callBaseCost fork cold + callee.accessCost + newAccountCost + callValueCost fork call.value

/-- The state gas that a call of kind `kind` pays for the account it creates, at fork `fork`.

From Glamsterdam, CALL with value to a dead account pays the state gas of a new account.

Other calls, and calls before Glamsterdam, pay none. -/
def callNewAccountStateGas (fork : Fork) (kind : CallKind) (state : State.TransactionState)
    (call : CallOperands) : Nat :=
  if fork ≥ .glamsterdam ∧ kind = .call ∧ call.value ≠ 0 ∧ ¬state.isAccountAlive call.address then
    GasCosts.NEW_ACCOUNT_STATE_GAS
  else 0

/-- The step of a call once it has paid `evm`, which passes on `subCall` gas.

CALL with a value fails in a frame that must not change the state.

Then memory grows by `expandBy` bytes, and the frame passes on its whole reservoir.

A frame that lacks the value runs no message.

It gets back the gas, the reservoir, and the `newAccount` state gas it paid. -/
def finishCall (kind : CallKind) (call : CallOperands) (callee : Callee)
    (subCall newAccount expandBy : Nat) (evm : Evm fork Meter) :
    Except EvmError (StepResult fork Meter) :=
  if kind = .call ∧ evm.message.isStatic ∧ call.value ≠ 0 then .error .writeInStaticContext
  else
    let reservoir := GasMeter.reservoir evm.gas
    let evm :=
      { evm with memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
    let current := evm.message.currentTarget
    let evm := recordAccountRead evm current
    if (evm.state.getAccount current).balance < call.value then
      .next <$> skipCall (refillStateGas evm newAccount) subCall reservoir
    else
      let to := if kind = .call ∨ kind = .staticcall then call.address else current
      let message : Message fork :=
        { blockEnv := evm.message.blockEnv
          txEnv := evm.message.txEnv
          caller := if kind = .delegatecall then evm.message.caller else current
          target := some to
          currentTarget := to
          gas := subCall
          reservoir
          value := if kind = .delegatecall then evm.message.value else call.value
          data := memoryReadBytes evm.memory call.inputStart.toNat call.inputSize.toNat
          codeAddress := some callee.codeAddress
          code := callee.code
          depth := evm.message.depth + 1
          shouldTransferValue := kind != .delegatecall
          isStatic := kind == .staticcall || evm.message.isStatic
          disablePrecompiles := callee.delegated }
      genericCall evm message newAccount call.outputStart call.outputSize

/-- The frame after a call of kind `kind` pays, and the gas that the call passes on.

The call pays its extra price `extraGas`, the growth of memory, and the gas it passes on.

From Glamsterdam, CALL pays its extra price and memory first, then `newAccount` state gas.

The gas it passes on is then a part of the execution gas left after both. -/
def payCall (kind : CallKind) (call : CallOperands) (memoryCost extraGas newAccount : Nat)
    (evm : Evm fork Meter) : Except EvmError (Nat × Evm fork Meter) := do
  if fork ≥ .glamsterdam ∧ kind = .call then
    let evm ← chargeGas evm (extraGas + memoryCost)
    let evm ← chargeStateGas evm newAccount
    let callGas := messageCallGas fork call.value call.gas.toNat (GasMeter.gasLeft evm.gas) 0 0
    let evm ← chargeGas evm callGas.cost
    return (callGas.subCall, evm)
  else
    let callGas :=
      messageCallGas fork call.value call.gas.toNat (GasMeter.gasLeft evm.gas) memoryCost extraGas
    let evm ← chargeGas evm (callGas.cost + memoryCost)
    return (callGas.subCall, evm)

/-- The step of a call of kind `kind`.

It pops its operands, accesses the address and a delegate, and pays.

It pays its extra price, the gas it passes on, and the growth of memory for both ranges.

From Glamsterdam, CALL with value in a frame that must not change the state fails first.

From Glamsterdam, the frame must then hold the price it knows before it reads the address.

That price is the access, the price of the value and the growth of memory, by EIP-7928.

The reads of the address and of a delegate stay even when the call then halts. -/
def callStep (kind : CallKind) (evm : Evm fork Meter) :
    Except EvmError (StepResult fork Meter) := do
  let (call, evm) ← popCallOperands kind evm
  if fork ≥ .glamsterdam ∧ kind = .call ∧ evm.message.isStatic ∧ call.value ≠ 0 then
    throw .writeInStaticContext
  let ranges := [(call.inputStart, call.inputSize), (call.outputStart, call.outputSize)]
  let growth := extendMemory evm.memory.size ranges
  let (cold, evm) := accessAddress evm call.address
  let known := callBaseCost fork cold + callValueCost fork call.value + growth.cost
  checkGas evm known
  let evm := recordAccountRead evm call.address
  keepReads evm .next do
    let (callee, evm) ← accessDelegation evm call.address known
    keepReads evm .next do
      let extraGas := callExtraGas fork kind evm.state call cold callee
      let newAccount := callNewAccountStateGas fork kind evm.state call
      let (subCall, evm) ← payCall kind call growth.cost extraGas newAccount evm
      finishCall kind call callee subCall newAccount growth.expandBy evm

/-- The instruction of a call opcode at fork `fork`.

Other opcodes give none, and so do DELEGATECALL before Homestead and STATICCALL before Byzantium. -/
def callInstruction (fork : Fork) :
    Op → Option (Evm fork Meter → Except EvmError (StepResult fork Meter))
  | .call => some (callStep .call)
  | .callcode => some (callStep .callcode)
  | .delegatecall => if .homestead ≤ fork then some (callStep .delegatecall) else none
  | .staticcall => if .byzantium ≤ fork then some (callStep .staticcall) else none
  | _ => none

/-! ## Each call lowers the measure of the frame -/

/-- The pops of the operands of a call pay nothing. -/
theorem popCallOperands_pays {kind : CallKind} {evm after : Evm fork Meter}
    {call : CallOperands} (h : popCallOperands kind evm = .ok (call, after)) :
    Pays 0 evm after := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e6⟩, h6, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e7⟩, h7, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have p3 : Pays 0 e2 e3 := by
    unfold popCallValue at h3
    split at h3
    · exact popWord_pays h3
    · cases h3
      exact .of_eq rfl rfl
  exact (((((((popWord_pays h1).trans (popWord_pays h2)).trans p3).trans (popWord_pays h4)).trans
    (popWord_pays h5)).trans (popWord_pays h6)).trans (popWord_pays h7)).mono

/-- The access to a delegate pays nothing. -/
theorem accessDelegation_pays {evm after : Evm fork Meter} {address : Address} {known : Nat}
    {callee : Callee} (h : accessDelegation evm address known = .ok (callee, after)) :
    Pays 0 evm after := by
  obtain ⟨code, -, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (accessAddress_pays _ _).trans (recordAccountRead_pays _ _)
  · cases h
    exact .of_eq rfl rfl

/-- A call that runs no message gets back exactly its gas, and keeps running. -/
theorem skipCall_gasHeld [LawfulGasMeter Meter] {evm after : Evm fork Meter}
    {gas reservoir : Nat} (h : skipCall evm gas reservoir = .ok after) :
    GasMeter.gasHeld after.gas = GasMeter.gasHeld evm.gas + gas ∧ after.running = evm.running := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  obtain ⟨_, -, h1⟩ := Base.bind_ok_iff.mp h1
  cases h1
  exact ⟨LawfulGasMeter.gasHeld_credit _ _ _, rfl⟩

/-- The caller gets back at most the gas that its callee holds, and keeps running. -/
theorem resumeCall_gasHeld [LawfulGasMeter Meter] {caller child after : Evm fork Meter}
    {newAccount : Nat} {outputStart outputSize : U256}
    (h : resumeCall fork caller newAccount outputStart outputSize child = .ok after) :
    GasMeter.gasHeld after.gas ≤ GasMeter.gasHeld caller.gas + GasMeter.gasHeld child.gas ∧
      after.running = caller.running := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  obtain ⟨_, -, h1⟩ := Base.bind_ok_iff.mp h1
  cases h1
  have g := gasHeld_incorporateChild caller child
  have r := running_incorporateChild caller child
  dsimp only
  split
  · exact ⟨Nat.le_of_eq g, r⟩
  · exact ⟨Nat.le_trans (LawfulGasMeter.gasHeld_refill _ _) (Nat.le_of_eq g), r⟩

/-- A call that runs no message after it paid more than its gas lowers the measure. -/
theorem skipCall_measure_lt [LawfulGasMeter Meter] {before evm after : Evm fork Meter}
    {gas reservoir cost : Nat} (paid : Pays cost before evm) (lt : gas < cost)
    (running : before.running = true) (h : skipCall evm gas reservoir = .ok after) :
    measure after < measure before := by
  have := paid.gasHeld
  obtain ⟨g, r⟩ := skipCall_gasHeld h
  exact Pays.measure_lt ⟨by omega, r.trans paid.running⟩ running

/-- A call that paid more than the gas of its message lowers the measure of the frame. -/
theorem genericCall_decreases [LawfulGasMeter Meter] {before evm : Evm fork Meter}
    {message : Message fork} {newAccount : Nat} {outputStart outputSize : U256} {cost : Nat}
    {result : StepResult fork Meter} (paid : Pays cost before evm) (lt : message.gas < cost)
    (running : before.running = true)
    (h : genericCall evm message newAccount outputStart outputSize = .ok result) :
    result.Decreases before := by
  have := paid.gasHeld
  unfold genericCall at h
  dsimp only at h
  split at h
  · cases hs : skipCall (refillStateGas { evm with returnData := .empty } newAccount) message.gas
        message.reservoir with
    | error => simp [hs, Functor.map, Except.map] at h
    | ok after =>
      simp only [hs, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      refine skipCall_measure_lt ?_ lt running hs
      exact (paid.congr (c := { evm with returnData := .empty }) rfl rfl).trans
        (refillStateGas_pays _ _) |>.mono (Nat.le_add_right _ _)
  · cases h
    refine ⟨by omega, fun child after used resumed => ?_⟩
    obtain ⟨g, r⟩ := resumeCall_gasHeld resumed
    exact Pays.measure_lt ⟨by simp only at g; omega, r.trans paid.running⟩ running

/-- A call that paid more than the gas it passes on lowers the measure of the frame. -/
theorem finishCall_decreases [LawfulGasMeter Meter] {kind : CallKind} {call : CallOperands}
    {callee : Callee} {subCall newAccount expandBy cost : Nat} {before evm : Evm fork Meter}
    {result : StepResult fork Meter} (paid : Pays cost before evm) (lt : subCall < cost)
    (running : before.running = true)
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    result.Decreases before := by
  unfold finishCall at h
  split at h
  · cases h
  · dsimp only at h
    have drained := ((paid.congr (c := { evm with memory := memoryExtend evm.memory expandBy })
      rfl rfl).drain).trans (recordAccountRead_pays _ evm.message.currentTarget)
    split at h
    · cases hs : skipCall (refillStateGas (recordAccountRead
          { evm with memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
          evm.message.currentTarget) newAccount) subCall (GasMeter.reservoir evm.gas) with
      | error => simp [hs, Functor.map, Except.map] at h
      | ok after =>
        simp only [hs, Functor.map, Except.map, Except.ok.injEq] at h
        subst h
        exact skipCall_measure_lt ((drained.trans (refillStateGas_pays _ _)).mono
          (Nat.le_add_right _ _)) lt running hs
    · exact genericCall_decreases (drained.mono (Nat.le_add_right _ _)) lt running h

/-- The price of the access of a call is at least 1 at every fork. -/
theorem one_le_callBaseCost (fork : Fork) (cold : Bool) : 1 ≤ callBaseCost fork cold := by
  unfold callBaseCost accountAccessCost gasSchedule
  repeat' split
  all_goals decide

/-- The extra price of a call is positive, and exceeds the stipend when the call sends value. -/
theorem callExtraGas_bounds {kind : CallKind} {state : State.TransactionState}
    {call : CallOperands} {cold : Bool} {callee : Callee} :
    0 < callExtraGas fork kind state call cold callee ∧
      (call.value ≠ 0 → GasCosts.CALL_STIPEND < callExtraGas fork kind state call cold callee) := by
  have := one_le_callBaseCost fork cold
  refine ⟨by unfold callExtraGas; dsimp only; omega, fun hv => ?_⟩
  have := stipend_lt_callValueCost (fork := fork) hv
  unfold callExtraGas
  dsimp only
  omega

/-- A call pays more than the gas it passes on, at every fork and for every kind of call.

That holds when its extra price is positive, and exceeds the stipend of a call with value. -/
theorem payCall_pays [LawfulGasMeter Meter] {kind : CallKind} {call : CallOperands}
    {memoryCost extraGas newAccount subCall : Nat} {evm after : Evm fork Meter}
    (pos : 0 < extraGas) (above : call.value ≠ 0 → GasCosts.CALL_STIPEND < extraGas)
    (h : payCall kind call memoryCost extraGas newAccount evm = .ok (subCall, after)) :
    ∃ cost, subCall < cost ∧ Pays cost evm after := by
  unfold payCall at h
  split at h
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    refine ⟨_, ?_, ((chargeGas_pays h1).trans (chargeStateGas_pays h2)).trans (chargeGas_pays h3)⟩
    rw [subCall_eq_cost_add_stipend]
    split
    · omega
    · have := above ‹_›
      omega
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    cases h
    refine ⟨_, ?_, chargeGas_pays h1⟩
    have := subCall_lt_cost (fork := fork) (gas := call.gas.toNat)
      (gasLeft := GasMeter.gasLeft evm.gas) (memoryCost := memoryCost)
      (stipend := GasCosts.CALL_STIPEND) pos above
    omega

/-- Each call lowers the measure of a running frame. -/
theorem callStep_decreases [LawfulGasMeter Meter] {kind : CallKind} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (running : evm.running = true)
    (h : callStep kind evm = .ok result) : result.Decreases evm := by
  obtain ⟨⟨call, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · cases h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  have p2 : Pays 0 e1 e2 := by
    have := accessAddress_pays e1 call.address
    rwa [hacc] at this
  rw [hacc] at h
  dsimp only at h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  have halted : ∀ (x : Evm fork Meter) e, (StepResult.next (exceptionalHalt x e)).Decreases evm :=
    fun x e => by
      show measure _ < measure evm
      rw [measure_exceptionalHalt]
      simp [measure, running]
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨⟨callee, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨⟨subCall, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨pos, above⟩ := callExtraGas_bounds (fork := fork) (kind := kind) (state := e3.state)
        (call := call) (cold := cold) (callee := callee)
      obtain ⟨cost, lt, p4⟩ := payCall_pays pos above h4
      have paid := ((((popCallOperands_pays h1).trans p2).trans
        (recordAccountRead_pays _ call.address)).trans (accessDelegation_pays h3)).trans p4
      exact finishCall_decreases (paid.mono (by omega)) lt running h
    · exact halted _ _
  · exact halted _ _

/-- Each call instruction lowers the measure of a running frame. -/
theorem callInstruction_decreases [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hrun : callInstruction fork op = some run)
    (h : run evm = .ok result) (running : evm.running = true) : result.Decreases evm := by
  cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hrun
  all_goals first
    | (subst hrun; exact callStep_decreases running h)
    | (split at hrun
       · simp only [Option.some.injEq] at hrun
         subst hrun
         exact callStep_decreases running h
       · cases hrun)

end EthLib.Execution.Evm
