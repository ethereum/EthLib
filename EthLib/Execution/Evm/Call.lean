module

public import EthLib.Execution.Evm.CallGas
public import EthLib.Execution.Evm.Delegation
public import EthLib.Execution.Evm.Measure

/-!
# `Evm.Call`

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

A callee gets less gas than the call pays, so each call lowers the measure of the frame.

Appendix H.2 of the Yellow Paper, Shanghai version, defines these instructions.

Its appendix Anomalies on the Main Network records the account at 0x03 that stays touched.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

The EIPs that add or change an instruction define it:

- [EIP-7][eip7], DELEGATECALL
- [EIP-211][eip211], the return data of a call
- [EIP-214][eip214], STATICCALL
- [EIP-2929][eip2929], the cold and warm accesses
- [EIP-7702][eip7702], the delegation indicator

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip7]: https://eips.ethereum.org/EIPS/eip-7#specification
[eip211]: https://eips.ethereum.org/EIPS/eip-211#specification
[eip214]: https://eips.ethereum.org/EIPS/eip-214#specification
[eip2929]: https://eips.ethereum.org/EIPS/eip-2929#specification
[eip7702]: https://eips.ethereum.org/EIPS/eip-7702#delegation-indicator
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256 toAddressMasked)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The greatest depth of a message: a call or a creation at this depth runs no message. -/
def STACK_DEPTH_LIMIT : Nat := 1024

/-! ## The caller after its callee -/

/-- The address of the RIPEMD-160 precompile, 0x03. -/
def RIPEMD160_ADDRESS : Address := Vector.ofFn fun i => if i.val = 19 then 3 else 0

/-- The accounts that a failed message leaves touched, from Spurious Dragon to Paris.

A failed message undoes its touches, except one: the precompile at 0x03 stays touched.

Block 2675119 of the main network deleted that empty account after a call to it ran out of gas.

The rule keeps that history, and applies when the child touched 0x03 or was a call to it. -/
def touchedOnError (fork : Fork) (caller child : Evm fork Meter) : Std.ExtTreeSet Address :=
  let touched := caller.substate.touchedAccounts
  if fork ≥ .spuriousDragon ∧ fork < .paris ∧
      (RIPEMD160_ADDRESS ∈ child.substate.touchedAccounts ∨
        (child.message.currentTarget = RIPEMD160_ADDRESS ∧
          child.state.accountExistsAndIsEmpty RIPEMD160_ADDRESS)) then
    touched.insert RIPEMD160_ADDRESS
  else touched

/-- The accounts that a successful message leaves touched.

From Spurious Dragon to Paris, they gain those of the child, and its target when that is empty. -/
def touchedOnSuccess (fork : Fork) (caller child : Evm fork Meter) : Std.ExtTreeSet Address :=
  let touched := caller.substate.touchedAccounts
  if fork ≥ .spuriousDragon ∧ fork < .paris then
    let touched := touched.insertMany child.substate.touchedAccounts.toList
    if child.state.accountExistsAndIsEmpty child.message.currentTarget then
      touched.insert child.message.currentTarget
    else touched
  else touched

/-- The calling frame after the message it ran ends with the frame `child`.

The caller gets back the gas left of the child, and the state that the child leaves.

A child that succeeds also passes on its logs, its refund, its accounts to delete and its accesses.

A child that fails passes on none of them. -/
def incorporateChild (fork : Fork) (caller child : Evm fork Meter) : Evm fork Meter :=
  let gas := GasMeter.credit caller.gas (GasMeter.gasLeft child.gas)
  if child.error.isNone then
    { caller with
      gas
      state := child.state
      substate := {
        accountsToDelete :=
          caller.substate.accountsToDelete.insertMany child.substate.accountsToDelete.toList
        logs := caller.substate.logs ++ child.substate.logs
        touchedAccounts := touchedOnSuccess fork caller child
        refundCounter := caller.substate.refundCounter + child.substate.refundCounter
        accessedAddresses := child.substate.accessedAddresses
        accessedStorageKeys := child.substate.accessedStorageKeys } }
  else
    { caller with
      gas
      state := child.state
      substate := { caller.substate with touchedAccounts := touchedOnError fork caller child } }

/-- The caller gets back exactly the gas left of the child. -/
theorem gasLeft_incorporateChild [LawfulGasMeter Meter] (caller child : Evm fork Meter) :
    GasMeter.gasLeft (incorporateChild fork caller child).gas =
      GasMeter.gasLeft caller.gas + GasMeter.gasLeft child.gas := by
  unfold incorporateChild
  split <;> exact LawfulGasMeter.gasLeft_credit _ _

/-- The caller runs after its callee exactly when it ran before. -/
theorem running_incorporateChild (caller child : Evm fork Meter) :
    (incorporateChild fork caller child).running = caller.running := by
  unfold incorporateChild
  split <;> rfl

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

Before Pectra, the call runs the code of the account at `address`. -/
def accessDelegation (evm : Evm fork Meter) (address : Address) :
    Except EvmError (Callee × Evm fork Meter) := do
  let code ← accountCode evm address
  let delegate := if fork ≥ .pectra then delegatedAddress code else none
  match delegate with
  | some delegate =>
    let (cold, evm) := accessAddress evm delegate
    let code ← accountCode evm delegate
    return (⟨delegate, code, true, accountAccessCost fork cold⟩, evm)
  | none => return (⟨address, code, false, 0⟩, evm)

/-- The frame after a call that runs no message: it gets back `gas`, and pushes 0.

The return data is empty. -/
def skipCall (evm : Evm fork Meter) (gas : Nat) : Except EvmError (Evm fork Meter) := do
  let evm ← pushWord { evm with gas := GasMeter.credit evm.gas gas, returnData := .empty } 0
  return advance evm

/-- The calling frame `caller` once its callee ends with the frame `child`.

It pushes 1 when the callee succeeded, and 0 when it failed or reverted.

The output of the callee becomes the return data.

The start of that output fills the output range of memory, as far as either goes. -/
def resumeCall (fork : Fork) (caller : Evm fork Meter) (outputStart outputSize : U256)
    (child : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let evm := { incorporateChild fork caller child with returnData := child.output }
  let evm ← pushWord evm (if child.error.isNone then 1 else 0)
  let output := child.output.extract 0 (min outputSize.toNat child.output.size)
  return advance { evm with memory := memoryWrite evm.memory outputStart.toNat output }

/-- The step of a call that has paid: run `message` first, unless the depth forbids it.

The call empties the return data.

A frame at the greatest depth runs no message: it gets back the gas of the message. -/
def genericCall (evm : Evm fork Meter) (message : Message fork) (outputStart outputSize : U256) :
    Except EvmError (StepResult fork Meter) :=
  let evm := { evm with returnData := .empty }
  if evm.message.depth + 1 > STACK_DEPTH_LIMIT then .next <$> skipCall evm message.gas
  else .ok (.child evm message (resumeCall fork evm outputStart outputSize))

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
  callBaseCost fork cold + callee.accessCost + newAccountCost + callValueCost call.value

/-- The step of a call once it has paid `evm`, which passes on `subCall` gas.

CALL with a value fails in a frame that must not change the state.

Then memory grows by `expandBy` bytes.

A frame that lacks the value runs no message. -/
def finishCall (kind : CallKind) (call : CallOperands) (callee : Callee) (subCall expandBy : Nat)
    (evm : Evm fork Meter) : Except EvmError (StepResult fork Meter) :=
  if kind = .call ∧ evm.message.isStatic ∧ call.value ≠ 0 then .error .writeInStaticContext
  else
    let evm := { evm with memory := memoryExtend evm.memory expandBy }
    let current := evm.message.currentTarget
    if (evm.state.getAccount current).balance < call.value then
      .next <$> skipCall evm subCall
    else
      let to := if kind = .call ∨ kind = .staticcall then call.address else current
      let message : Message fork :=
        { blockEnv := evm.message.blockEnv
          txEnv := evm.message.txEnv
          caller := if kind = .delegatecall then evm.message.caller else current
          target := some to
          currentTarget := to
          gas := subCall
          value := if kind = .delegatecall then evm.message.value else call.value
          data := memoryReadBytes evm.memory call.inputStart.toNat call.inputSize.toNat
          codeAddress := some callee.codeAddress
          code := callee.code
          depth := evm.message.depth + 1
          shouldTransferValue := kind != .delegatecall
          isStatic := kind == .staticcall || evm.message.isStatic
          disablePrecompiles := callee.delegated }
      genericCall evm message call.outputStart call.outputSize

/-- The step of a call of kind `kind`.

It pops its operands, accesses the address and a delegate, and pays.

It pays its extra price, the gas it passes on, and the growth of memory for both ranges. -/
def callStep (kind : CallKind) (evm : Evm fork Meter) :
    Except EvmError (StepResult fork Meter) := do
  let (call, evm) ← popCallOperands kind evm
  let ranges := [(call.inputStart, call.inputSize), (call.outputStart, call.outputSize)]
  let growth := extendMemory evm.memory.size ranges
  let (cold, evm) := accessAddress evm call.address
  let (callee, evm) ← accessDelegation evm call.address
  let extraGas := callExtraGas fork kind evm.state call cold callee
  let callGas :=
    messageCallGas fork call.value call.gas.toNat (GasMeter.gasLeft evm.gas) growth.cost extraGas
  let evm ← chargeGas evm (callGas.cost + growth.cost)
  finishCall kind call callee callGas.subCall growth.expandBy evm

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
  obtain ⟨⟨_, e1⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, e5⟩, h5, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, e6⟩, h6, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, e7⟩, h7, h⟩ := except_bind_eq_ok h
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
theorem accessDelegation_pays {evm after : Evm fork Meter} {address : Address} {callee : Callee}
    (h : accessDelegation evm address = .ok (callee, after)) : Pays 0 evm after := by
  obtain ⟨code, -, h⟩ := except_bind_eq_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := except_bind_eq_ok h
    cases h
    exact accessAddress_pays _ _
  · cases h
    exact .of_eq rfl rfl

/-- A call that runs no message gets back exactly its gas, and keeps running. -/
theorem skipCall_gasLeft [LawfulGasMeter Meter] {evm after : Evm fork Meter} {gas : Nat}
    (h : skipCall evm gas = .ok after) :
    GasMeter.gasLeft after.gas = GasMeter.gasLeft evm.gas + gas ∧ after.running = evm.running := by
  obtain ⟨_, h1, h⟩ := except_bind_eq_ok h
  cases h
  obtain ⟨_, -, h1⟩ := except_bind_eq_ok h1
  cases h1
  exact ⟨LawfulGasMeter.gasLeft_credit _ _, rfl⟩

/-- The caller gets back exactly the gas left of its callee, and keeps running. -/
theorem resumeCall_gasLeft [LawfulGasMeter Meter] {caller child after : Evm fork Meter}
    {outputStart outputSize : U256}
    (h : resumeCall fork caller outputStart outputSize child = .ok after) :
    GasMeter.gasLeft after.gas = GasMeter.gasLeft caller.gas + GasMeter.gasLeft child.gas ∧
      after.running = caller.running := by
  obtain ⟨_, h1, h⟩ := except_bind_eq_ok h
  cases h
  obtain ⟨_, -, h1⟩ := except_bind_eq_ok h1
  cases h1
  exact ⟨gasLeft_incorporateChild caller child, running_incorporateChild caller child⟩

/-- A call that runs no message after it paid more than its gas lowers the measure. -/
theorem skipCall_measure_lt [LawfulGasMeter Meter] {before evm after : Evm fork Meter}
    {gas cost : Nat} (paid : Pays cost before evm) (lt : gas < cost)
    (running : before.running = true) (h : skipCall evm gas = .ok after) :
    measure after < measure before := by
  have := paid.gasLeft
  obtain ⟨g, r⟩ := skipCall_gasLeft h
  exact Pays.measure_lt ⟨by omega, r.trans paid.running⟩ running

/-- A call that paid more than the gas of its message lowers the measure of the frame. -/
theorem genericCall_decreases [LawfulGasMeter Meter] {before evm : Evm fork Meter}
    {message : Message fork} {outputStart outputSize : U256} {cost : Nat}
    {result : StepResult fork Meter} (paid : Pays cost before evm) (lt : message.gas < cost)
    (running : before.running = true)
    (h : genericCall evm message outputStart outputSize = .ok result) :
    result.Decreases before := by
  have := paid.gasLeft
  unfold genericCall at h
  dsimp only at h
  split at h
  · cases hs : skipCall { evm with returnData := .empty } message.gas with
    | error => simp [hs, Functor.map, Except.map] at h
    | ok after =>
      simp only [hs, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      refine skipCall_measure_lt ?_ lt running hs
      exact paid.congr rfl rfl
  · cases h
    refine ⟨by omega, fun child after used resumed => ?_⟩
    obtain ⟨g, r⟩ := resumeCall_gasLeft resumed
    exact Pays.measure_lt ⟨by simp only at g; omega, r.trans paid.running⟩ running

/-- A call that paid more than the gas it passes on lowers the measure of the frame. -/
theorem finishCall_decreases [LawfulGasMeter Meter] {kind : CallKind} {call : CallOperands}
    {callee : Callee} {subCall expandBy cost : Nat} {before evm : Evm fork Meter}
    {result : StepResult fork Meter} (paid : Pays cost before evm) (lt : subCall < cost)
    (running : before.running = true)
    (h : finishCall kind call callee subCall expandBy evm = .ok result) :
    result.Decreases before := by
  unfold finishCall at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases hs : skipCall { evm with memory := memoryExtend evm.memory expandBy } subCall with
      | error => simp [hs, Functor.map, Except.map] at h
      | ok after =>
        simp only [hs, Functor.map, Except.map, Except.ok.injEq] at h
        subst h
        refine skipCall_measure_lt ?_ lt running hs
        exact paid.congr rfl rfl
    · refine genericCall_decreases ?_ lt running h
      exact paid.congr rfl rfl

/-- The price of the access of a call is at least 1 at every fork. -/
theorem one_le_callBaseCost (fork : Fork) (cold : Bool) : 1 ≤ callBaseCost fork cold := by
  unfold callBaseCost accountAccessCost gasSchedule
  repeat' split
  all_goals decide

/-- A callee gets less gas than its call pays, at every fork and for every kind of call. -/
theorem subCall_lt_cost_callExtraGas {kind : CallKind} {state : State.TransactionState}
    {call : CallOperands} {cold : Bool} {callee : Callee} {gas gasLeft memoryCost : Nat} :
    (messageCallGas fork call.value gas gasLeft memoryCost
        (callExtraGas fork kind state call cold callee)).subCall <
      (messageCallGas fork call.value gas gasLeft memoryCost
        (callExtraGas fork kind state call cold callee)).cost := by
  have := one_le_callBaseCost fork cold
  refine subCall_lt_cost (by unfold callExtraGas; dsimp only; omega) fun hv => ?_
  have := stipend_lt_callValueCost hv
  unfold callExtraGas
  dsimp only
  omega

/-- Each call lowers the measure of a running frame. -/
theorem callStep_decreases [LawfulGasMeter Meter] {kind : CallKind} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (running : evm.running = true)
    (h : callStep kind evm = .ok result) : result.Decreases evm := by
  obtain ⟨⟨call, e1⟩, h1, h⟩ := except_bind_eq_ok h
  dsimp only at h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  have p2 : Pays 0 e1 e2 := by
    have := accessAddress_pays e1 call.address
    rwa [hacc] at this
  rw [hacc] at h
  dsimp only at h
  obtain ⟨⟨callee, e3⟩, h3, h⟩ := except_bind_eq_ok h
  obtain ⟨e4, h4, h⟩ := except_bind_eq_ok h
  have paid := (((popCallOperands_pays h1).trans p2).trans (accessDelegation_pays h3)).trans
    (chargeGas_pays h4)
  refine finishCall_decreases ?_ subCall_lt_cost_callExtraGas running h
  exact paid.mono (by omega)

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
