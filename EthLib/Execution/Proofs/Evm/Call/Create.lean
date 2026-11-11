module

public import EthLib.Execution.Evm.Call.MessageCall
public import EthLib.Execution.Proofs.Evm.Call.Instructions
public import EthLib.Execution.Proofs.Evm.Gas.StateGas

/-!
# Proofs: `Evm.Call.Create`

From Glamsterdam, a creation costs 12000 execution gas, and a dead new address 183600 state gas.

No creation pays state gas before Glamsterdam.

A creation that fails its first checks leaves the state and the accessed addresses as they were.

A creation whose init code fails gives back the state gas of the new account.

From Glamsterdam, the code of a creation costs 1530 state gas a byte.

No creation deploys code longer than 65536 bytes from Glamsterdam.

A creation keeps the size of memory a multiple of 32, and so does the creator once it ends.

So does every instruction that may send a message.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256)
open EthLib.Execution.State (TransactionState)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## Prices -/

/-- From Glamsterdam, a creation costs 12000 before memory, init code and hash. -/
theorem createBaseCost_of_glamsterdam (h : fork ≥ .glamsterdam) : createBaseCost fork = 12000 := by
  simp only [createBaseCost, h, ite_true]
  rfl

/-- Before Glamsterdam, a creation costs 32000 before memory, init code and hash. -/
theorem createBaseCost_of_lt (h : fork < .glamsterdam) : createBaseCost fork = 32000 := by
  have : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt h
  simp only [createBaseCost, this, ite_false]
  rfl

/-- Before Glamsterdam, a creation pays no state gas. -/
theorem createNewAccountStateGas_of_lt (h : fork < .glamsterdam) (state : TransactionState)
    (address : Address) : createNewAccountStateGas fork state address = 0 := by
  have : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt h
  simp only [createNewAccountStateGas, this, false_and, ite_false]

/-- From Glamsterdam, a creation pays the state gas of a new account exactly at a dead address. -/
theorem createNewAccountStateGas_of_glamsterdam (h : fork ≥ .glamsterdam)
    (state : TransactionState) (address : Address) :
    createNewAccountStateGas fork state address =
      if state.isAccountAlive address then 0 else NEW_ACCOUNT_STATE_GAS := by
  by_cases alive : state.isAccountAlive address <;>
    simp [createNewAccountStateGas, h, alive]

/-! ## The first checks -/

/-- A creation that fails its first checks runs no message.

It pushes 0 and keeps its gas and its substate, so it accesses no new address.

Its state only records the read of the sender. -/
theorem launchCreate_of_preflight {evm : Evm fork Meter} {value : U256} {initCode : ByteArray}
    {salt : Option U256} {result : StepResult fork Meter}
    (fails : (evm.state.getAccount evm.message.currentTarget).balance < value ∨
      (evm.state.getAccount evm.message.currentTarget).nonce = MAX_NONCE ∨
      evm.message.depth + 1 > STACK_DEPTH_LIMIT)
    (h : launchCreate evm value initCode salt = .ok result) :
    ∃ after, result = .next after ∧
      after.state = evm.state.recordAccountRead evm.message.currentTarget ∧
      after.substate = evm.substate ∧ after.gas = GasMeter.credit evm.gas 0 0 := by
  unfold launchCreate at h
  dsimp only at h
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by exact fails))] at h
  cases hs : skipCall (recordAccountRead { evm with returnData := .empty }
      evm.message.currentTarget) 0 0 with
  | error => simp [hs, Functor.map, Except.map] at h
  | ok after =>
    simp only [hs, Functor.map, Except.map, Except.ok.injEq] at h
    refine ⟨after, h.symm, ?_⟩
    obtain ⟨_, h1, h2⟩ := Base.bind_ok_iff.mp hs
    cases h2
    obtain ⟨_, -, h1⟩ := Base.bind_ok_iff.mp h1
    cases h1
    exact ⟨rfl, rfl, rfl⟩

omit [GasMeter Meter] in
/-- Popping the salt of a creation takes the top word for CREATE2, and none for CREATE.

It keeps the context of the frame, and its memory. -/
theorem popSalt_eq_ok {create2 : Bool} {evm after : Evm fork Meter} {salt : Option U256}
    (h : popSalt create2 evm = .ok (salt, after)) :
    salt = (if create2 then evm.stack.val.head? else none) ∧
      SameContext evm after ∧ after.memory = evm.memory := by
  unfold popSalt at h
  cases create2
  · cases h
    exact ⟨rfl, SameContext.refl _, rfl⟩
  · obtain ⟨⟨_, _⟩, hp, h⟩ := Base.bind_ok_iff.mp h
    cases h
    obtain ⟨hst, hmem, -⟩ := popWord_eq_ok hp
    rw [hst]
    exact ⟨rfl, popWord_sameContext hp, hmem⟩

/-- A creation after payment succeeds only in a non-static frame whose init code fits the limit.

It then runs the creation step that has paid. -/
theorem genericCreate_eq_ok {evm : Evm fork Meter} {value : U256} {initCode : ByteArray}
    {salt : Option U256} {result : StepResult fork Meter}
    (h : genericCreate evm value initCode salt = .ok result) :
    (fork ≥ .shapella → initCode.size ≤ maxInitCodeSize fork) ∧
      evm.message.isStatic = false ∧
      launchCreate evm value initCode salt = .ok result := by
  unfold genericCreate at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hlim hstatic
  refine ⟨fun hs => Nat.not_lt.mp fun hlt => hlim ⟨hs, hlt⟩, ?_, h⟩
  revert hstatic
  cases evm.message.isStatic <;> simp

/-- A successful step of CREATE or CREATE2 pops its operands, pays, grows memory and launches. -/
theorem createStep_eq_ok {create2 : Bool} {evm : Evm fork Meter} {result : StepResult fork Meter}
    (h : createStep create2 evm = .ok result) :
    ∃ value start size rest paid,
      evm.stack.val = value :: start :: size :: rest ∧
      SameContext evm paid ∧
      paid.memory =
        memoryExtend evm.memory (extendMemory evm.memory.size [(start, size)]).expandBy ∧
      evm.message.isStatic = false ∧
      (fork ≥ .shapella →
        (memoryReadBytes paid.memory start.toNat size.toNat).size ≤ maxInitCodeSize fork) ∧
      launchCreate paid value (memoryReadBytes paid.memory start.toNat size.toNat)
        (if create2 then rest.head? else none) = .ok result := by
  unfold createStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp [hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  rw [ite_eq_right_of_eq_false _ _ (eq_false hs)] at h
  obtain ⟨⟨value, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨start, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨size, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨salt, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨paid, h5, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨hsalt, sc4, m4⟩ := popSalt_eq_ok h4
  obtain ⟨hlim, hstatic, hlaunch⟩ := genericCreate_eq_ok h
  obtain ⟨s1, m1, -⟩ := popWord_eq_ok h1
  obtain ⟨s2, m2, -⟩ := popWord_eq_ok h2
  obtain ⟨s3, m3, -⟩ := popWord_eq_ok h3
  have sc : SameContext evm paid := (((((popWord_sameContext h1).trans
    (popWord_sameContext h2)).trans (popWord_sameContext h3)).trans sc4).trans
    (chargeGasAndMemory_sameContext h5))
  have hm4 : e4.memory = evm.memory := m4.trans (m3.trans (m2.trans m1))
  have hmem : paid.memory =
      memoryExtend evm.memory (extendMemory evm.memory.size [(start, size)]).expandBy := by
    rw [memory_chargeGasAndMemory h5, hm4]
  refine ⟨value, start, size, e3.stack.val, paid, ?_, sc, hmem, sc.message ▸ hstatic, hlim,
    hsalt ▸ hlaunch⟩
  rw [s1, s2, s3]

/-! ## The refill -/

/-- A creation whose init code fails gives the caller back `newAccount` state gas. -/
theorem resumeCreate_gas_of_error {caller child after : Evm fork Meter} {newAccount : Nat}
    {address : Address} (failed : child.error.isSome)
    (h : resumeCreate fork caller newAccount address child = .ok after) :
    after.gas = GasMeter.refill (GasMeter.absorb caller.gas child.gas false) newAccount := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  obtain ⟨_, -, h1⟩ := Base.bind_ok_iff.mp h1
  cases h1
  have hn : child.error.isNone = false := by
    cases e : child.error <;> simp_all
  simp only [advance, hn, Bool.false_eq_true, ite_false, refillStateGas, incorporateChild]

/-- A creation whose init code succeeds gives the caller back its gas, and no state gas. -/
theorem resumeCreate_gas_of_success {caller child after : Evm fork Meter} {newAccount : Nat}
    {address : Address} (ok : child.error = none)
    (h : resumeCreate fork caller newAccount address child = .ok after) :
    after.gas = GasMeter.absorb caller.gas child.gas true := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  obtain ⟨_, -, h1⟩ := Base.bind_ok_iff.mp h1
  cases h1
  simp only [advance, ok, Option.isNone_none, ite_true, incorporateChild]

/-! ## The code -/

/-- From Glamsterdam, the code of `size` bytes raises the net state gas by 1530 a byte. -/
theorem stateGasUsed_chargeCodeDeposit (h : fork ≥ .glamsterdam) {meter after : StateGasMeter}
    {size : Nat} (hc : chargeCodeDeposit fork meter size = .ok after) :
    after.stateGasUsed = meter.stateGasUsed + size * 1530 := by
  simp only [chargeCodeDeposit, h, ite_true] at hc
  obtain ⟨charged, h1, h2⟩ := Base.bind_ok_iff.mp hc
  rw [StateGasMeter.stateGasUsed_chargeState h2]
  simp only [GasMeter.charge, StateGasMeter.charge] at h1
  split at h1
  · cases h1
  · cases h1
    simp only [StateGasMeter.stateGasUsed, CPSB]
    omega

/-- From Glamsterdam, a creation that deploys its code deploys at most 65536 bytes. -/
theorem depositCode_size_le (h : fork ≥ .glamsterdam) {snapshot : TransactionState}
    {evm after : Evm fork Meter} (hd : depositCode fork snapshot evm = .ok after)
    (ok : after.error = none) : evm.output.size ≤ 65536 := by
  have hm : maxCodeSize fork = some 65536 := by simp only [maxCodeSize, h, ite_true]
  unfold depositCode at hd
  dsimp only at hd
  split at hd
  · cases hd
    rename_i failed
    simp_all
  split at hd
  · cases hd
    simp at ok
  split at hd
  · cases hd
    simp at ok
  · rename_i _ fits
    simp only [hm, Option.any_some, decide_eq_true_eq, h, true_and, Nat.not_lt] at fits
    exact fits

/-! ## The size of memory -/

/-- The creator keeps its memory once the creation ends. -/
theorem memory_resumeCreate {caller child after : Evm fork Meter} {newAccount : Nat}
    {address : Address} (h : resumeCreate fork caller newAccount address child = .ok after) :
    after.memory = caller.memory := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have hc : (incorporateChild fork caller child).memory = caller.memory := by
    unfold incorporateChild
    split <;> rfl
  simp only [advance, memory_pushWord h1]
  split <;> exact hc

/-- A creation that has paid keeps the size of memory a multiple of 32.

So does the creator once the creation ends. -/
theorem memoryAligned_launchCreate {evm : Evm fork Meter} {value : U256} {initCode : ByteArray}
    {salt : Option U256} {result : StepResult fork Meter} (hmod : evm.memory.size % 32 = 0)
    (h : launchCreate evm value initCode salt = .ok result) : result.MemoryAligned := by
  unfold launchCreate at h
  dsimp only at h
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    obtain ⟨stack, -, rfl⟩ := skipCall_eq_ok hs
    exact hmod
  obtain ⟨address, -, h⟩ := Base.bind_ok_iff.mp h
  refine memoryAligned_keepReads ?_ (fun r hr => ?_) h
  · simp only [recordAccountRead, memory_accessAddress]
    exact hmod
  obtain ⟨e1, h1, hr⟩ := Base.bind_ok_iff.mp hr
  obtain ⟨e2, h2, hr⟩ := Base.bind_ok_iff.mp hr
  obtain ⟨state, -, hr⟩ := Base.bind_ok_iff.mp hr
  have m2 : e2.memory = evm.memory := by
    rw [memory_chargeGas h2, memory_chargeStateGas h1]
    exact memory_accessAddress _ _
  split at hr
  · cases hr
    intro child after hresume
    rw [memory_resumeCreate hresume]
    exact m2 ▸ hmod
  · obtain ⟨e3, h3, hr⟩ := Base.bind_ok_iff.mp hr
    cases hr
    show (advance e3).memory.size % 32 = 0
    rw [show (advance e3).memory = e3.memory from rfl, memory_pushWord h3]
    exact m2 ▸ hmod

/-- A creation keeps the size of memory a multiple of 32, and so does the creator after it.

It grows memory for its init code before the init code runs. -/
theorem memoryAligned_createStep {create2 : Bool} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hmod : evm.memory.size % 32 = 0)
    (h : createStep create2 evm = .ok result) : result.MemoryAligned := by
  obtain ⟨_, start, size, _, paid, -, -, hmem, -, -, hlaunch⟩ := createStep_eq_ok h
  exact memoryAligned_launchCreate (hmem ▸ size_memoryExtend_mod hmod [(start, size)]) hlaunch

/-- Each creation keeps the size of memory a multiple of 32, and so does the creator after it. -/
theorem memoryAligned_createInstruction {op : Op}
    {step : Evm fork Meter → Except EvmError (StepResult fork Meter)}
    (hstep : createInstruction fork op = some step) {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hmod : evm.memory.size % 32 = 0)
    (h : step evm = .ok result) : result.MemoryAligned := by
  cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep)
  all_goals first
    | exact memoryAligned_createStep hmod h
    | (subst hstep; exact memoryAligned_createStep hmod h)
    | cases hstep

/-- Each instruction that may send a message keeps the size of memory a multiple of 32.

So does the frame that sends it, once the message ends. -/
theorem memoryAligned_messageInstruction {op : Op}
    {step : Evm fork Meter → Except EvmError (StepResult fork Meter)}
    (hstep : messageInstruction fork op = some step) {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hmod : evm.memory.size % 32 = 0)
    (h : step evm = .ok result) : result.MemoryAligned := by
  unfold messageInstruction at hstep
  cases hc : callInstruction (Meter := Meter) fork op with
  | some call =>
    rw [hc] at hstep
    cases hstep
    exact memoryAligned_callInstruction hc hmod h
  | none =>
    rw [hc] at hstep
    exact memoryAligned_createInstruction hstep hmod h

end EthLib.Execution.Evm
