module

public import EthLib.Execution.Proofs.Evm.Instructions.AccountData
public import EthLib.Execution.Proofs.Evm.Instructions.ControlFlow
public import EthLib.Execution.Proofs.Evm.Instructions.EnvironmentData
public import EthLib.Execution.Proofs.Evm.Instructions.LogData
public import EthLib.Execution.Proofs.Evm.Instructions.MemoryData
public import EthLib.Execution.Proofs.Evm.Instructions.Return
public import EthLib.Execution.Proofs.Evm.Instructions.SelfDestruct
public import EthLib.Execution.Proofs.Evm.Instructions.StackOnly
public import EthLib.Execution.Proofs.Evm.Instructions.Storage
public import EthLib.Execution.Proofs.Evm.Instructions.TransientStorage
public import EthLib.Execution.Proofs.Evm.Interpreter
public import EthLib.Execution.Proofs.State.Frame

/-!
# Proofs: the instructions in a frame that must not change the state

A step of a frame that must not change the state leaves its state as it was.

Only the records of the reads of the frame differ.

The step also keeps the message, the code and the block of the frame.

The account, the storage and the transient storage of every address read as before.

That holds for the instructions of each of the ten groups that give the next frame.

The instructions that write fail in such a frame: SSTORE, TSTORE, LOG and SELFDESTRUCT.

Before Glamsterdam, SSTORE and SELFDESTRUCT halt the frame with the reads that they made.

From Glamsterdam, they fail before any read.

The calls and the creations are not here.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256 toAddressMasked)
open EthLib.Execution.State.TransactionState (SameOutside)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- A step leaves the state as it was, up to the records of its reads. -/
def StateKept (before after : Evm fork Meter) : Prop :=
  SameOutside [] before.state after.state

omit [GasMeter Meter] in
/-- A frame keeps its own state. -/
theorem StateKept.refl (evm : Evm fork Meter) : StateKept evm evm :=
  State.TransactionState.SameOutside.refl _ _

omit [GasMeter Meter] in
/-- Two steps that each keep the state keep it together. -/
theorem StateKept.trans {a b c : Evm fork Meter} (hab : StateKept a b) (hbc : StateKept b c) :
    StateKept a c :=
  fun address hmem => by
    obtain ⟨x, y, z⟩ := hab address hmem
    obtain ⟨x', y', z'⟩ := hbc address hmem
    exact ⟨x'.trans x, fun key => (y' key).trans (y key), fun key => (z' key).trans (z key)⟩

omit [GasMeter Meter] in
/-- A step that keeps the whole state keeps it. -/
theorem StateKept.of_sameContext {a b : Evm fork Meter} (h : SameContext a b) : StateKept a b := by
  unfold StateKept
  rw [h.state]
  exact StateKept.refl a

omit [GasMeter Meter] in
/-- A record of the read of an account keeps the state. -/
theorem stateKept_recordAccountRead (evm : Evm fork Meter) (address : Address) :
    StateKept evm (recordAccountRead evm address) :=
  State.TransactionState.sameOutside_recordAccountRead evm.state address

omit [GasMeter Meter] in
/-- A move of the program counter keeps the state. -/
theorem StateKept.advance {a b : Evm fork Meter} (h : StateKept a b) (n : Nat := 1) :
    StateKept a (Evm.advance b n) := h

omit [GasMeter Meter] in
/-- An access to an address keeps the state. -/
theorem stateKept_accessAddress (evm : Evm fork Meter) (address : Address) :
    StateKept evm (accessAddress evm address).2 := by
  obtain ⟨_, h⟩ := accessAddress_snd evm address
  rw [h]
  exact StateKept.refl _

omit [GasMeter Meter] in
/-- An access to a storage key keeps the state. -/
theorem stateKept_accessStorageKey (evm : Evm fork Meter) (address : Address)
    (key : Bytes32) : StateKept evm (accessStorageKey evm address key).2 := by
  obtain ⟨_, h⟩ := accessStorageKey_snd evm address key
  rw [h]
  exact StateKept.refl _

omit [GasMeter Meter] in
/-- A record of the read of a storage key keeps the state. -/
theorem stateKept_recordStorageRead (evm : Evm fork Meter) (address : Address) (key : Bytes32) :
    StateKept evm (recordStorageRead evm address key) :=
  State.TransactionState.sameOutside_recordStorageRead evm.state address key

/-- A step of a static frame keeps its state, up to the records of its reads.

It keeps its message, its code and the block of its state. -/
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
    StaticStep evm (accessAddress evm address).2 := by
  obtain ⟨_, h⟩ := accessAddress_snd evm address
  exact ⟨stateKept_accessAddress evm address, by rw [h], by rw [h], by rw [h]⟩

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

end EthLib.Execution.Evm
