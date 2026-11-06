module

public import EthLib.Execution.Proofs.Evm.Call.Create
public import EthLib.Execution.Proofs.Evm.Call.Instructions
public import EthLib.Execution.Proofs.Evm.Instructions.Static

/-!
# Proofs: the steps of a frame that must not change the state

A step of such a frame keeps its message, its code and its state, up to the records of its reads.

That holds through the calls and their returns, for the four kinds of call.

A call sends a static message that runs the code of a callee.

The code of a callee comes from an account that holds code, also through a delegation.

A value that a call sends goes to its own sender, whose account holds code.

A frame that resumes after its callee ends keeps its state, if the callee changed it by reads only.

A creation never completes in such a frame.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256 toAddressMasked)
open EthLib.Execution.State (EMPTY_CODE_HASH)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- A step of a static frame keeps its state, up to the records of its reads.

It keeps its message and its code. -/
structure StaticStep (before after : Evm fork Meter) : Prop where
  state : StateKept before after
  message : after.message = before.message
  code : after.code = before.code
  parent : after.state.parent = before.state.parent

omit [GasMeter Meter] in
/-- A frame keeps its state and message. -/
theorem StaticStep.refl (evm : Evm fork Meter) : StaticStep evm evm :=
  ⟨StateKept.refl _, rfl, rfl, rfl⟩

omit [GasMeter Meter] in
/-- Two steps that each keep the state and the message keep them together. -/
theorem StaticStep.trans {a b c : Evm fork Meter} (hab : StaticStep a b) (hbc : StaticStep b c) :
    StaticStep a c :=
  ⟨hab.state.trans hbc.state, hbc.message.trans hab.message, hbc.code.trans hab.code,
    hbc.parent.trans hab.parent⟩

omit [GasMeter Meter] in
/-- A step that keeps the message, the state and the substate is a static step. -/
theorem StaticStep.of_sameContext {a b : Evm fork Meter} (h : SameContext a b) : StaticStep a b :=
  ⟨StateKept.of_sameContext h, h.message, h.code, by rw [h.state]⟩

omit [GasMeter Meter] in
/-- A change of the memory is a static step. -/
theorem StaticStep.withMemory (evm : Evm fork Meter) (memory : ByteArray) :
    StaticStep evm { evm with memory } := ⟨StateKept.refl _, rfl, rfl, rfl⟩

omit [GasMeter Meter] in
/-- A move of the program counter is a static step. -/
theorem StaticStep.advance {a b : Evm fork Meter} (h : StaticStep a b) (n : Nat := 1) :
    StaticStep a (Evm.advance b n) := ⟨h.state, h.message, h.code, h.parent⟩

omit [GasMeter Meter] in
/-- A record of the read of an account is a static step. -/
theorem staticStep_recordAccountRead (evm : Evm fork Meter) (address : Address) :
    StaticStep evm (recordAccountRead evm address) :=
  ⟨stateKept_recordAccountRead evm address, rfl, rfl, rfl⟩

omit [GasMeter Meter] in
/-- A record of the read of a storage key is a static step. -/
theorem staticStep_recordStorageRead (evm : Evm fork Meter) (address : Address) (key : Bytes32) :
    StaticStep evm (recordStorageRead evm address key) :=
  ⟨stateKept_recordStorageRead evm address key, rfl, rfl, rfl⟩

omit [GasMeter Meter] in
/-- An access to an address is a static step. -/
theorem staticStep_accessAddress (evm : Evm fork Meter) (address : Address) :
    StaticStep evm (accessAddress evm address).2 :=
  ⟨stateKept_accessAddress evm address, accessAddress_message evm address,
    by obtain ⟨_, h⟩ := accessAddress_snd evm address; rw [h],
    by obtain ⟨_, h⟩ := accessAddress_snd evm address; rw [h]⟩

omit [GasMeter Meter] in
/-- An access to a storage key is a static step. -/
theorem staticStep_accessStorageKey (evm : Evm fork Meter) (address : Address) (key : Bytes32) :
    StaticStep evm (accessStorageKey evm address key).2 := by
  obtain ⟨_, h⟩ := accessStorageKey_snd evm address key
  exact ⟨stateKept_accessStorageKey evm address key, by rw [h], by rw [h], by rw [h]⟩

/-- An exceptional halt is a static step. -/
theorem staticStep_exceptionalHalt (evm : Evm fork Meter) (e : EvmError) :
    StaticStep evm (exceptionalHalt evm e) := ⟨StateKept.refl _, rfl, rfl, rfl⟩

/-- BALANCE is a static step. -/
theorem staticStep_balanceStep {evm after : Evm fork Meter} (h : balanceStep evm = .ok after) :
    StaticStep evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : StaticStep e1 e2 := by
    have := staticStep_accessAddress e1 (toAddressMasked w)
    rwa [hacc] at this
  exact ((((StaticStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (StaticStep.of_sameContext (chargeGas_sameContext h3))).trans
    (staticStep_recordAccountRead _ _)).trans
    (StaticStep.of_sameContext (pushWord_sameContext h4)) |>.advance

/-- EXTCODESIZE is a static step. -/
theorem staticStep_extcodesizeStep {evm after : Evm fork Meter}
    (h : extcodesizeStep evm = .ok after) : StaticStep evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨code, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : StaticStep e1 e2 := by
    have := staticStep_accessAddress e1 (toAddressMasked w)
    rwa [hacc] at this
  exact ((((StaticStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (StaticStep.of_sameContext (chargeGas_sameContext h3))).trans
    (staticStep_recordAccountRead _ _)).trans
    (StaticStep.of_sameContext (pushWord_sameContext h5)) |>.advance

/-- EXTCODEHASH is a static step. -/
theorem staticStep_extcodehashStep {evm after : Evm fork Meter}
    (h : extcodehashStep evm = .ok after) : StaticStep evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : StaticStep e1 e2 := by
    have := staticStep_accessAddress e1 (toAddressMasked w)
    rwa [hacc] at this
  exact ((((StaticStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (StaticStep.of_sameContext (chargeGas_sameContext h3))).trans
    (staticStep_recordAccountRead _ _)).trans
    (StaticStep.of_sameContext (pushWord_sameContext h4)) |>.advance

/-- EXTCODECOPY is a static step. -/
theorem staticStep_extcodecopyStep {evm after : Evm fork Meter}
    (h : extcodecopyStep evm = .ok after) : StaticStep evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨st, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨off, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨sz, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e4 (toAddressMasked w) with ⟨cold, e5⟩
  simp only [hacc] at h
  obtain ⟨e6, h6, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨code, h7, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : StaticStep e4 e5 := by
    have := staticStep_accessAddress e4 (toAddressMasked w)
    rwa [hacc] at this
  exact (((((((StaticStep.of_sameContext (popWord_sameContext h1)).trans
    (StaticStep.of_sameContext (popWord_sameContext h2))).trans
    (StaticStep.of_sameContext (popWord_sameContext h3))).trans
    (StaticStep.of_sameContext (popWord_sameContext h4))).trans ha).trans
    (StaticStep.of_sameContext (chargeGasAndMemory_sameContext h6))).trans
    (staticStep_recordAccountRead _ _)).trans (StaticStep.withMemory _ _) |>.advance

/-- Each instruction that reads another account is a static step. -/
theorem staticStep_accountStep {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : accountStep fork op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : StaticStep evm after := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hstep
  case balance => subst hstep; exact staticStep_balanceStep h
  case extcodesize => subst hstep; exact staticStep_extcodesizeStep h
  case extcodecopy => subst hstep; exact staticStep_extcodecopyStep h
  case selfbalance =>
    split at hstep
    · cases hstep
      exact (staticStep_recordAccountRead _ _).trans
        (StaticStep.of_sameContext (readFrame_sameContext h))
    · cases hstep
  case extcodehash =>
    split at hstep
    · cases hstep; exact staticStep_extcodehashStep h
    · cases hstep

/-- SLOAD is a static step. -/
theorem staticStep_sloadStep {evm after : Evm fork Meter} (h : sloadStep evm = .ok after) :
    StaticStep evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  rcases hacc : accessStorageKey e1 e1.message.currentTarget (U256.toBeBytes w) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : StaticStep e1 e2 := by
    have := staticStep_accessStorageKey e1 e1.message.currentTarget (U256.toBeBytes w)
    rwa [hacc] at this
  exact ((((StaticStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (StaticStep.of_sameContext (chargeGas_sameContext h3))).trans
    (staticStep_recordStorageRead _ _ _)).trans
    (StaticStep.of_sameContext (pushWord_sameContext h4)) |>.advance

/-- SSTORE in a static frame is a static step.

Before Glamsterdam it halts the frame with its reads.

From Glamsterdam it fails before any read. -/
theorem staticStep_sstoreStep_of_isStatic {evm after : Evm fork Meter}
    (static : evm.message.isStatic = true) (h : sstoreStep evm = .ok after) :
    StaticStep evm after := by
  unfold sstoreStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨⟨k, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨n, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  have c2 := (StaticStep.of_sameContext (popWord_sameContext h1)).trans
    (StaticStep.of_sameContext (popWord_sameContext h2))
  have m2 : e2.message = evm.message :=
    (popWord_sameContext h2).message.trans (popWord_sameContext h1).message
  simp only [] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨keys, hacc⟩ := accessStorageKey_snd e2 e2.message.currentTarget (U256.toBeBytes k)
      rcases hpair : accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k) with
        ⟨cold, e3⟩
      rw [hpair] at hacc
      simp only [hpair] at h
      obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
      have m5 : e5.message = evm.message := by
        obtain ⟨_, -, h5⟩ := Base.bind_ok_iff.mp h5
        cases h5
        rw [(chargeGas_sameContext h4).message]
        cases hacc
        exact m2
      simp [m5, static, throw, throwThe, MonadExceptOf.throw] at h
    · rcases hpair : accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k) with
        ⟨cold, e3⟩
      have ha : StaticStep e2 e3 := by
        have := staticStep_accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k)
        rwa [hpair] at this
      exact ((c2.trans ha).trans (staticStep_recordStorageRead _ _ _)).trans
        (staticStep_exceptionalHalt _ _)

/-- Each instruction that uses storage is a static step in a static frame. -/
theorem staticStep_storageStep_of_isStatic {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : storageStep op = some step) {evm after : Evm fork Meter}
    (static : evm.message.isStatic = true) (h : step evm = .ok after) : StaticStep evm after := by
  cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hstep
  case sload => subst hstep; exact staticStep_sloadStep h
  case sstore => subst hstep; exact staticStep_sstoreStep_of_isStatic static h

/-- SELFDESTRUCT in a static frame is a static step.

Before Glamsterdam it halts the frame with its reads.

From Glamsterdam it fails before any read. -/
theorem staticStep_selfdestructStep_of_isStatic {evm after : Evm fork Meter}
    (static : evm.message.isStatic = true) (h : selfdestructStep fork evm = .ok after) :
    StaticStep evm after := by
  unfold selfdestructStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [hs, and_self, ↓reduceIte] at h
    cases h
  simp only [hs, ↓reduceIte] at h
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha : StaticStep e1 e2 := by
    have := staticStep_accessAddress e1 (toAddressMasked w)
    rwa [hacc] at this
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  have c := ((StaticStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (staticStep_recordAccountRead e2 (toAddressMasked w))
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    have m4 : e4.message = evm.message := by
      rw [(chargeStateGas_sameContext h4).message, (chargeGas_sameContext h3).message]
      exact c.message
    unfold finishSelfdestruct at h
    simp [m4, static] at h
  · exact c.trans (staticStep_exceptionalHalt _ _)

/-- Each instruction of transient storage is a static step in a static frame. -/
theorem staticStep_transientStorageStep_of_isStatic {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : transientStorageStep fork op = some step) {evm after : Evm fork Meter}
    (static : evm.message.isStatic = true) (h : step evm = .ok after) : StaticStep evm after := by
  cases op <;> simp only [transientStorageStep, reduceCtorEq] at hstep <;> split at hstep <;>
    simp only [Option.some.injEq, reduceCtorEq] at hstep <;> subst hstep
  case tload => exact StaticStep.of_sameContext (tloadStep_sameContext h)
  case tstore => exact absurd h (tstoreStep_ne_ok_of_isStatic static)

/-- RETURN and REVERT are static steps. -/
theorem staticStep_returnOpStep {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : returnOpStep fork op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : StaticStep evm after := by
  cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hstep
  case «return» => subst hstep; exact StaticStep.of_sameContext (returnStep_sameContext h)
  case revert =>
    split at hstep
    · cases hstep; exact StaticStep.of_sameContext (revertStep_sameContext h)
    · cases hstep

/-- The instruction of SELFDESTRUCT is a static step in a static frame. -/
theorem staticStep_selfdestructOpStep_of_isStatic {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : selfdestructOpStep fork op = some step) {evm after : Evm fork Meter}
    (static : evm.message.isStatic = true) (h : step evm = .ok after) : StaticStep evm after := by
  cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  exact staticStep_selfdestructStep_of_isStatic static h

/-- The instructions of LOG are static steps in a static frame, as none completes. -/
theorem staticStep_logOpStep_of_isStatic {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : logOpStep op = some step) {evm after : Evm fork Meter}
    (static : evm.message.isStatic = true) (h : step evm = .ok after) : StaticStep evm after := by
  cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  exact absurd h (logStep_ne_ok_of_isStatic static)

/-- Each instruction that gives the next frame is a static step in a static frame. -/
theorem staticStep_instruction_of_isStatic {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hrun : instruction fork op = some run) (static : evm.message.isStatic = true)
    (h : run evm = .ok after) : StaticStep evm after := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact StaticStep.of_sameContext (stackOnlyStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact StaticStep.of_sameContext (controlFlowStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact StaticStep.of_sameContext (memoryDataStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact staticStep_returnOpStep hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact StaticStep.of_sameContext (environmentStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact staticStep_accountStep hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact staticStep_storageStep_of_isStatic hf static h
  rcases orElse_eq_some hrun with hf | hrun
  · exact staticStep_transientStorageStep_of_isStatic hf static h
  rcases orElse_eq_some hrun with hf | hf
  · exact staticStep_logOpStep_of_isStatic hf static h
  · exact staticStep_selfdestructOpStep_of_isStatic hf static h

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
  exact ⟨StateKept.refl _, rfl, rfl, rfl⟩

/-- The caller that takes in a child has the state of the child. -/
theorem state_incorporateChild (caller child : Evm fork Meter) :
    (incorporateChild fork caller child).state = child.state := by
  unfold incorporateChild
  split <;> rfl

/-- The caller that takes in a child keeps its message. -/
theorem code_incorporateChild (caller child : Evm fork Meter) :
    (incorporateChild fork caller child).code = caller.code := by
  unfold incorporateChild
  split <;> rfl

/-- The caller that takes in a child keeps its message. -/
theorem message_incorporateChild (caller child : Evm fork Meter) :
    (incorporateChild fork caller child).message = caller.message := by
  unfold incorporateChild
  split <;> rfl

/-- A caller that resumes after a callee whose state it keeps keeps its own state. -/
theorem staticStep_resumeCall {caller child after : Evm fork Meter} {newAccount : Nat}
    {outputStart outputSize : U256}
    (h : resumeCall fork caller newAccount outputStart outputSize child = .ok after)
    (kept : StateKept caller child) (parent : child.state.parent = caller.state.parent) :
    StaticStep caller after := by
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have hp := pushWord_sameContext h1
  have hs : e.state = child.state := by
    rw [hp.state]
    split <;> simp [state_incorporateChild, refillStateGas]
  have hm : e.message = caller.message := by
    rw [hp.message]
    split <;> simp [message_incorporateChild, refillStateGas]
  have hc : e.code = caller.code := by
    rw [hp.code]
    split <;> simp [code_incorporateChild, refillStateGas]
  refine ⟨?_, hm, hc, ?_⟩
  · show State.TransactionState.SameOutside [] caller.state e.state
    rw [hs]
    exact kept
  · show e.state.parent = caller.state.parent
    rw [hs]
    exact parent

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

/-- The child of a step of a static frame: a static message.

The caller keeps its state and message.

When the child ends with a state that differs from the caller's only by reads:

the caller that resumes keeps its state and message. -/
def StaticChild (evm caller : Evm fork Meter) (message : Message fork)
    (resume : Evm fork Meter → Except EvmError (Evm fork Meter)) : Prop :=
  StaticStep evm caller ∧ StaticMessage caller.state message ∧
    ∀ child after, resume child = .ok after → StateKept caller child →
      child.state.parent = caller.state.parent → StaticStep evm after

/-- What a step of a static frame gives: the next frame, or a static child. -/
def StaticResult (evm : Evm fork Meter) : StepResult fork Meter → Prop
  | .next after => StaticStep evm after
  | .child caller message resume => StaticChild evm caller message resume

/-- A call that has paid gives a static step, or a static child. -/
theorem staticResult_genericCall {evm : Evm fork Meter} {message : Message fork}
    {newAccount : Nat} {outputStart outputSize : U256} {result : StepResult fork Meter}
    (hmsg : StaticMessage evm.state message)
    (h : genericCall evm message newAccount outputStart outputSize = .ok result) :
    StaticResult evm result := by
  unfold genericCall at h
  dsimp only at h
  split at h
  · cases hs : skipCall (refillStateGas { evm with returnData := .empty } newAccount)
        message.gas message.reservoir with
    | error e => simp [hs, Functor.map, Except.map] at h
    | ok after =>
      simp only [hs, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      have := staticStep_skipCall hs
      exact (⟨StateKept.refl _, rfl, rfl, rfl⟩ : StaticStep evm
        (refillStateGas { evm with returnData := .empty } newAccount)).trans this
  · cases h
    refine ⟨⟨?_, rfl, rfl, rfl⟩, hmsg, ?_⟩
    · exact StateKept.refl _
    · intro child after hres kept parent
      exact (⟨StateKept.refl _, rfl, rfl, rfl⟩ :
        StaticStep evm { evm with returnData := .empty }).trans
        (staticStep_resumeCall hres kept parent)

omit [GasMeter Meter] in
/-- A frame that is reached from a frame by a static step gives the same kinds of result. -/
theorem StaticResult.lift {evm evm' : Evm fork Meter} {result : StepResult fork Meter}
    (h : StaticStep evm evm') (r : StaticResult evm' result) : StaticResult evm result := by
  cases result with
  | next after => exact h.trans r
  | child caller message resume =>
    obtain ⟨c, m, m4⟩ := r
    exact ⟨h.trans c, m, fun child after hres kept parent =>
      h.trans (m4 child after hres kept parent)⟩

/-- A call in a static frame that has paid gives a static step, or a static child.

The frame must hold code at its own account.

The callee must hold code at the account called when it has code. -/
theorem staticResult_finishCall {kind : CallKind} {call : CallOperands} {callee : Callee}
    {subCall newAccount expandBy : Nat} {evm : Evm fork Meter} {result : StepResult fork Meter}
    (static : evm.message.isStatic = true) (hv : kind.sendsValue = false → call.value = 0)
    (self : (evm.state.getAccount evm.message.currentTarget).codeHash ≠ EMPTY_CODE_HASH)
    (hcallee : callee.code.size ≠ 0 →
      (evm.state.getAccount call.address).codeHash ≠ EMPTY_CODE_HASH)
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    StaticResult evm result := by
  unfold finishCall at h
  split at h
  · cases h
  rename_i hnot
  dsimp only at h
  have pre : StaticStep evm (recordAccountRead { evm with
      memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
      evm.message.currentTarget) := ⟨StateKept.refl _, rfl, rfl, rfl⟩
  split at h
  · cases hs : skipCall (refillStateGas (recordAccountRead { evm with
        memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
        evm.message.currentTarget) newAccount) subCall (GasMeter.reservoir evm.gas) with
    | error e => simp [hs, Functor.map, Except.map] at h
    | ok after =>
      simp only [hs, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      have refill : StaticStep (recordAccountRead { evm with
          memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
          evm.message.currentTarget)
          (refillStateGas (recordAccountRead { evm with
          memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
          evm.message.currentTarget) newAccount) := ⟨StateKept.refl _, rfl, rfl, rfl⟩
      exact (pre.trans refill).trans (staticStep_skipCall hs)
  · refine StaticResult.lift pre (staticResult_genericCall ?_ h)
    have hcall : kind = .call → call.value = 0 := by
      intro hk
      exact Decidable.byContradiction fun hne => hnot ⟨hk, static, hne⟩
    refine ⟨?_, rfl, ?_, ?_⟩
    · simp only [Bool.or_eq_true, beq_iff_eq]
      exact Or.inr static
    · intro nonempty
      cases kind
      · exact hcallee nonempty
      · exact self
      · exact self
      · exact hcallee nonempty
    · intro htransfer hvalue
      cases kind
      · exact absurd (hcall rfl) (by simpa using hvalue)
      · exact ⟨rfl, self⟩
      · simp at htransfer
      · exact absurd (hv rfl) (by simpa using hvalue)

omit [GasMeter Meter] in
/-- A static step keeps every account. -/
theorem getAccount_of_staticStep {a b : Evm fork Meter} (h : StaticStep a b)
    (address : Address) : b.state.getAccount address = a.state.getAccount address := by
  have := (h.state address (by simp)).1
  simp [State.TransactionState.getAccount, this]

/-- Each call in a static frame gives a static step, or a static child.

The frame must hold code at its own account. -/
theorem staticResult_callStep {kind : CallKind} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (static : evm.message.isStatic = true)
    (self : (evm.state.getAccount evm.message.currentTarget).codeHash ≠ EMPTY_CODE_HASH)
    (h : callStep kind evm = .ok result) : StaticResult evm result := by
  unfold callStep at h
  obtain ⟨⟨call, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨c1, hv⟩ := staticStep_popCallOperands h1
  dsimp only at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    cases h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha : StaticStep e1 e2 := by
    have := staticStep_accessAddress e1 call.address
    rwa [hacc] at this
  have s3 : StaticStep evm (recordAccountRead e2 call.address) :=
    (c1.trans ha).trans (staticStep_recordAccountRead e2 call.address)
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨⟨callee, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
    have s4 : StaticStep evm e4 := s3.trans (staticStep_accessDelegation h4)
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨⟨subCall, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
      have s5 : StaticStep evm e5 := s4.trans (staticStep_payCall h5)
      refine StaticResult.lift s5 (staticResult_finishCall (by rw [s5.message]; exact static) hv
        ?_ ?_ h)
      · rw [getAccount_of_staticStep s5, s5.message]
        exact self
      · intro nonempty
        have := accessDelegation_codeHash_ne h4 nonempty
        rw [getAccount_of_staticStep ((staticStep_accessDelegation h4).trans
          (staticStep_payCall h5)) call.address]
        exact this
    · exact s4.trans (staticStep_exceptionalHalt _ _)
  · exact s3.trans (staticStep_exceptionalHalt _ _)

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

/-- Each instruction that may send a message gives a static step or a static child. -/
theorem staticResult_messageInstruction {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hrun : messageInstruction fork op = some run)
    (static : evm.message.isStatic = true)
    (self : (evm.state.getAccount evm.message.currentTarget).codeHash ≠ EMPTY_CODE_HASH)
    (h : run evm = .ok result) : StaticResult evm result := by
  unfold messageInstruction at hrun
  cases hc : callInstruction (Meter := Meter) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals first
      | (subst hc; exact staticResult_callStep static self h)
      | (split at hc
         · simp only [Option.some.injEq] at hc
           subst hc
           exact staticResult_callStep static self h
         · cases hc)
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun
    all_goals first
      | (subst hrun; exact absurd h (createStep_ne_ok_of_isStatic static))
      | (split at hrun
         · simp only [Option.some.injEq] at hrun
           subst hrun
           exact absurd h (createStep_ne_ok_of_isStatic static)
         · cases hrun)

/-- A step of a static frame gives a static step, or a static child.

The code of the frame is the code of its message, and runs at an account that holds code. -/
theorem staticResult_step {evm : Evm fork Meter} {result : StepResult fork Meter}
    (static : evm.message.isStatic = true) (hcode : evm.code = evm.message.code)
    (hhold : StaticCode evm.state evm.message) (h : step fork evm = .ok result) :
    StaticResult evm result := by
  unfold step at h
  split at h
  · rename_i hlt
    dsimp only at h
    split at h
    · cases h
    · split at h
      · rename_i hop
        cases hr : ‹Evm fork Meter → Except EvmError (Evm fork Meter)› evm with
        | error => simp [hr, Functor.map, Except.map] at h
        | ok after =>
          simp only [hr, Functor.map, Except.map, Except.ok.injEq] at h
          subst h
          exact staticStep_instruction_of_isStatic hop static hr
      · split at h
        · rename_i hcall
          refine staticResult_messageInstruction hcall static (hhold ?_) h
          rw [← hcode]
          omega
        · cases h
  · simp only [stopStep, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    exact StaticStep.of_sameContext (controlFlowStep_sameContext (op := .stop) rfl rfl)

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

section Loop

variable {step : Evm fork Meter → Except EvmError (StepResult fork Meter)}
  {decreases : ∀ {evm result}, evm.running = true → step evm = .ok result →
    result.Decreases evm}
  {bound : Nat} {runChild : MessageRunner fork Meter bound}

theorem staticStep_runFrame
    (next : ∀ {evm after : Evm fork Meter}, StaticFrame evm → step evm = .ok (.next after) →
      StaticStep evm after)
    (child : ∀ {evm caller : Evm fork Meter} {message : Message fork}
      {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}, StaticFrame evm →
      step evm = .ok (.child caller message resume) → StaticChild evm caller message resume)
    (runs : ∀ {caller : Evm fork Meter} {message : Message fork} {lt : message.gas < bound}
      {c : Evm fork Meter} {used : GasMeter.gasHeld c.gas ≤ message.gas},
      StaticFrame caller → StaticMessage caller.state message →
      runChild caller message lt = .ok ⟨c, used⟩ →
        StateKept caller c ∧ c.state.parent = caller.state.parent)
    {evm after : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound}
    (hf : StaticFrame evm)
    (h : runFrame step decreases bound runChild evm within = .ok after) : StaticStep evm after := by
  fun_induction runFrame step decreases bound runChild evm within
  case case1 => cases h
  case case2 => cases h; exact staticStep_exceptionalHalt _ _
  case case3 =>
    rename_i result _ ih
    have n := next hf result
    exact n.trans (ih (StaticFrame.of_staticStep n hf) h)
  case case4 => cases h
  case case5 => cases h
  case case6 => cases h; exact staticStep_exceptionalHalt _ _
  case case7 =>
    obtain ⟨c0, hmsg, hres⟩ := child hf ‹step _ = .ok (.child _ _ _)›
    obtain ⟨kept, parent⟩ := runs (StaticFrame.of_staticStep c0 hf) hmsg ‹runChild _ _ _ = .ok _›
    have n := hres _ _ (by assumption) kept parent
    exact n.trans (‹StaticFrame _ → runFrame _ _ _ _ _ _ = .ok after → StaticStep _ after›
      (StaticFrame.of_staticStep n hf) h)
  case case8 => cases h; exact StaticStep.refl _

end Loop

end EthLib.Execution.Evm
