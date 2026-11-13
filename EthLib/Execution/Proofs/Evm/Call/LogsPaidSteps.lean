module

public import EthLib.Execution.Proofs.Evm.Call.LogWeight
public import EthLib.Execution.Proofs.Evm.Call.Run
public import EthLib.Execution.Proofs.Evm.Call.StaticStep

/-!
# Proofs: no step raises the potential of logs and gas of its frame

The potential of a frame is four times the weight of its logs, plus the gas it holds.

A LOG step adds a log and pays at least four times its weight.

From Glamsterdam, SELFDESTRUCT may add a transfer log, and its price of at least 5000 covers it.

Every other step keeps the logs, and holds no more gas than before.

A call or a creation pays at least the gas of its message, plus the allowance of that message.

So the caller that resumes has at most its potential before.

That needs the child to end with at most its gas, plus its allowance.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256 toAddressMasked)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- Four times the weight of the logs of a frame, plus the gas it holds. -/
def logsPotential (evm : Evm fork Meter) : Nat :=
  4 * logsWeight evm.substate.logs.toList + GasMeter.gasHeld evm.gas

/-! ## The logs that a step keeps -/

omit [GasMeter Meter] in
/-- A step that keeps the context keeps the logs. -/
theorem SameContext.logs {a b : Evm fork Meter} (h : SameContext a b) :
    b.substate.logs = a.substate.logs := by
  rw [h.substate]

omit [GasMeter Meter] in
/-- An access to an address keeps the logs. -/
theorem logs_accessAddress (evm : Evm fork Meter) (address : Address) :
    (accessAddress evm address).2.substate.logs = evm.substate.logs := by
  unfold accessAddress
  split <;> rfl

omit [GasMeter Meter] in
/-- An access to a slot keeps the logs. -/
theorem logs_accessStorageKey (evm : Evm fork Meter) (address : Address) (key : Bytes32) :
    (accessStorageKey evm address key).2.substate.logs = evm.substate.logs := by
  unfold accessStorageKey
  split <;> rfl

/-- BALANCE keeps the logs. -/
theorem logs_balanceStep {evm after : Evm fork Meter} (h : balanceStep evm = .ok after) :
    after.substate.logs = evm.substate.logs := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  have ha := logs_accessAddress e1 (toAddressMasked w)
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  rw [hacc] at ha
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (pushWord_sameContext h4).logs.trans
    ((chargeGas_sameContext h3).logs.trans (ha.trans (popWord_sameContext h1).logs))

/-- EXTCODESIZE keeps the logs. -/
theorem logs_extcodesizeStep {evm after : Evm fork Meter} (h : extcodesizeStep evm = .ok after) :
    after.substate.logs = evm.substate.logs := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  have ha := logs_accessAddress e1 (toAddressMasked w)
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  rw [hacc] at ha
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨code, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (pushWord_sameContext h5).logs.trans
    ((chargeGas_sameContext h3).logs.trans (ha.trans (popWord_sameContext h1).logs))

/-- EXTCODECOPY keeps the logs. -/
theorem logs_extcodecopyStep {evm after : Evm fork Meter} (h : extcodecopyStep evm = .ok after) :
    after.substate.logs = evm.substate.logs := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  have ha := logs_accessAddress e4 (toAddressMasked w)
  rcases hacc : accessAddress e4 (toAddressMasked w) with ⟨cold, e5⟩
  rw [hacc] at ha
  simp only [hacc] at h
  obtain ⟨e6, h6, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨code, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (chargeGasAndMemory_sameContext h6).logs.trans (ha.trans
    ((popWord_sameContext h4).logs.trans ((popWord_sameContext h3).logs.trans
      ((popWord_sameContext h2).logs.trans (popWord_sameContext h1).logs))))

/-- EXTCODEHASH keeps the logs. -/
theorem logs_extcodehashStep {evm after : Evm fork Meter} (h : extcodehashStep evm = .ok after) :
    after.substate.logs = evm.substate.logs := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  have ha := logs_accessAddress e1 (toAddressMasked w)
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  rw [hacc] at ha
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (pushWord_sameContext h4).logs.trans
    ((chargeGas_sameContext h3).logs.trans (ha.trans (popWord_sameContext h1).logs))

/-- Each instruction that reads another account keeps the logs. -/
theorem logs_accountStep {op : Op} {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : accountStep fork op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : after.substate.logs = evm.substate.logs := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hstep
  case balance => subst hstep; exact logs_balanceStep h
  case extcodesize => subst hstep; exact logs_extcodesizeStep h
  case extcodecopy => subst hstep; exact logs_extcodecopyStep h
  case selfbalance =>
    split at hstep
    · cases hstep
      exact (readFrame_sameContext h).logs
    · cases hstep
  case extcodehash =>
    split at hstep
    · cases hstep; exact logs_extcodehashStep h
    · cases hstep

/-- SLOAD keeps the logs. -/
theorem logs_sloadStep {evm after : Evm fork Meter} (h : sloadStep evm = .ok after) :
    after.substate.logs = evm.substate.logs := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  have ha := logs_accessStorageKey e1 e1.message.currentTarget (U256.toBeBytes w)
  rcases hacc : accessStorageKey e1 e1.message.currentTarget (U256.toBeBytes w) with ⟨cold, e2⟩
  rw [hacc] at ha
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (pushWord_sameContext h4).logs.trans
    ((chargeGas_sameContext h3).logs.trans (ha.trans (popWord_sameContext h1).logs))

/-- SSTORE keeps the logs. -/
theorem logs_sstoreStep {evm after : Evm fork Meter} (h : sstoreStep evm = .ok after) :
    after.substate.logs = evm.substate.logs := by
  unfold sstoreStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨⟨k, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨n, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  have c2 := (popWord_sameContext h2).logs.trans (popWord_sameContext h1).logs
  dsimp only at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · have ha := logs_accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k)
    rcases hpair : accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k) with
      ⟨cold, e3⟩
    rw [hpair] at ha
    simp only [hpair] at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
      have m5 : e5.substate.logs = evm.substate.logs :=
        (chargeStateGas_sameContext h5).logs.trans ((chargeGas_sameContext h4).logs.trans
          (ha.trans c2))
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · obtain ⟨st, -, h⟩ := Base.bind_ok_iff.mp h
        cases h
        exact m5
    · exact ha.trans c2

/-- Each instruction that uses storage keeps the logs. -/
theorem logs_storageStep {op : Op} {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : storageStep op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : after.substate.logs = evm.substate.logs := by
  cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hstep
  case sload => subst hstep; exact logs_sloadStep h
  case sstore => subst hstep; exact logs_sstoreStep h

/-- TSTORE keeps the logs. -/
theorem logs_tstoreStep {evm after : Evm fork Meter} (h : tstoreStep evm = .ok after) :
    after.substate.logs = evm.substate.logs := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · cases h
    exact (chargeGas_sameContext h3).logs.trans
      ((popWord_sameContext h2).logs.trans (popWord_sameContext h1).logs)

/-- Each instruction of transient storage keeps the logs. -/
theorem logs_transientStorageStep {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : transientStorageStep fork op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : after.substate.logs = evm.substate.logs := by
  cases op <;> simp only [transientStorageStep, reduceCtorEq] at hstep <;> split at hstep <;>
    simp only [Option.some.injEq, reduceCtorEq] at hstep <;> subst hstep
  · exact (tloadStep_sameContext h).logs
  · exact logs_tstoreStep h

/-- RETURN and REVERT keep the logs. -/
theorem logs_returnOpStep {op : Op} {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : returnOpStep fork op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : after.substate.logs = evm.substate.logs := by
  cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hstep
  case «return» => subst hstep; exact (returnStep_sameContext h).logs
  case revert =>
    split at hstep
    · cases hstep; exact (revertStep_sameContext h).logs
    · cases hstep

/-! ## The potential after an instruction -/

/-- A frame with the logs of another and no more gas has no more potential. -/
theorem logsPotential_le_of_logs {a b : Evm fork Meter} (logs : b.substate.logs = a.substate.logs)
    (gas : GasMeter.gasHeld b.gas ≤ GasMeter.gasHeld a.gas) :
    logsPotential b ≤ logsPotential a := by
  unfold logsPotential
  rw [logs]
  omega

/-- LOGn pays at least four times the weight of its log, so it raises no potential. -/
theorem logsPotential_logStep [LawfulGasMeter Meter] {n : Nat} {evm after : Evm fork Meter}
    (h : logStep n evm = .ok after) : logsPotential after ≤ logsPotential evm := by
  obtain ⟨⟨st, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨sz, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨topics, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨hlen, c3⟩ := popTopics_eq_ok h3
  have c := (((popWord_sameContext h1).trans (popWord_sameContext h2)).trans c3).trans
    (chargeGasAndMemory_sameContext h4)
  have paid := ((((popWord_pays h1).trans (popWord_pays h2)).trans (popTopics_pays h3)).trans
    (chargeGasAndMemory_pays h4)).gasHeld
  have hd := size_memoryReadBytes_le e4.memory st.toNat sz.toNat
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · cases h
    simp only [logsPotential, advance, Array.toList_push, logsWeight_concat, logWeight, c.logs,
      hlen]
    simp only [logCost, OPCODE_LOG_BASE, OPCODE_LOG_DATA_PER_BYTE, OPCODE_LOG_TOPIC] at paid
    omega

/-- A move of ether adds at most the allowance of one transfer log, and only to another account.

The allowance is four times the weight of a transfer log. -/
theorem logsWeight_pushTransferLog (logs : Array Blocks.Log) (sender recipient : Address)
    (amount : U256) :
    4 * logsWeight (pushTransferLog fork logs sender recipient amount).toList ≤
      4 * logsWeight logs.toList +
        if amount ≠ 0 ∧ sender ≠ recipient then transferAllowance fork else 0 := by
  unfold pushTransferLog
  split
  · rename_i hc
    rw [Array.toList_push, logsWeight_concat, Nat.mul_add,
      ← transferAllowance_of_glamsterdam_le hc.1 sender recipient amount]
    split
    · exact Nat.le_refl _
    · exact absurd hc.2 ‹_›
  · omega

/-- SELFDESTRUCT pays at least the allowance of one transfer log. -/
theorem transferAllowance_le_selfdestructCost (cold createsAccount : Bool) :
    transferAllowance fork ≤ selfdestructCost fork cold createsAccount := by
  unfold transferAllowance
  split
  · rename_i hg
    have ht : fork ≥ .tangerineWhistle := Nat.le_trans (by decide) hg
    simp only [selfdestructCost, gasSchedule, ht, ↓reduceIte]
    omega
  · omega

/-- SELFDESTRUCT pays for its transfer log, so it raises no potential. -/
theorem logsPotential_selfdestructStep [LawfulGasMeter Meter] {evm after : Evm fork Meter}
    (h : selfdestructStep fork evm = .ok after) : logsPotential after ≤ logsPotential evm := by
  unfold selfdestructStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [hs, and_self, ↓reduceIte] at h
    cases h
  simp only [hs, ↓reduceIte] at h
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  have ha := logs_accessAddress e1 (toAddressMasked w)
  have pa := accessAddress_pays e1 (toAddressMasked w)
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  rw [hacc] at ha pa
  simp only [hacc] at h
  have l2 := ha.trans (popWord_sameContext h1).logs
  have p2 := (popWord_pays h1).trans pa
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    have paid := ((p2.trans (recordAccountRead_pays _ _)).trans (chargeGas_pays h3)).trans
      (chargeStateGas_pays h4)
    have g := paid.gasHeld
    have l4 : e4.substate.logs = evm.substate.logs :=
      (chargeStateGas_sameContext h4).logs.trans ((chargeGas_sameContext h3).logs.trans l2)
    unfold finishSelfdestruct at h
    split at h
    · cases h
    · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
      cases h
      have hw := logsWeight_pushTransferLog (fork := fork) e4.substate.logs
        e4.message.currentTarget (toAddressMasked w)
        (e4.state.getAccount e4.message.currentTarget).balance
      have hc := transferAllowance_le_selfdestructCost (fork := fork) cold
        (selfdestructCreatesAccount fork (recordAccountRead e2 (toAddressMasked w)).state
          (recordAccountRead e2 (toAddressMasked w)).message.currentTarget (toAddressMasked w))
      have l4' : logsWeight e4.substate.logs.toList = logsWeight evm.substate.logs.toList := by
        rw [l4]
      unfold logsPotential
      dsimp only
      split at hw <;> omega
  · exact logsPotential_le_of_logs l2 (by
      simp only [id, exceptionalHalt, LawfulGasMeter.gasHeld_exhaust]
      exact Nat.zero_le _)

/-- Each instruction that gives the next frame raises no potential of a running frame. -/
theorem logsPotential_instruction [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hrun : instruction fork op = some run) (h : run evm = .ok after)
    (running : evm.running = true) : logsPotential after ≤ logsPotential evm := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact logsPotential_le_of_logs (stackOnlyStep_sameContext hf h).logs
      (gasHeld_le_of_measure_lt (stackOnlyStep_measure_lt hf h running))
  rcases orElse_eq_some hrun with hf | hrun
  · exact logsPotential_le_of_logs (controlFlowStep_sameContext hf h).logs
      (gasHeld_le_of_measure_lt (controlFlowStep_measure_lt hf h running))
  rcases orElse_eq_some hrun with hf | hrun
  · exact logsPotential_le_of_logs (memoryDataStep_sameContext hf h).logs
      (gasHeld_le_of_measure_lt (memoryDataStep_measure_lt hf h running))
  rcases orElse_eq_some hrun with hf | hrun
  · exact logsPotential_le_of_logs (logs_returnOpStep hf h)
      (gasHeld_le_of_measure_lt (returnOpStep_measure_lt hf h running))
  rcases orElse_eq_some hrun with hf | hrun
  · exact logsPotential_le_of_logs (environmentStep_sameContext hf h).logs
      (gasHeld_le_of_measure_lt (environmentStep_measure_lt hf h running))
  rcases orElse_eq_some hrun with hf | hrun
  · exact logsPotential_le_of_logs (logs_accountStep hf h)
      (gasHeld_le_of_measure_lt (accountStep_measure_lt hf h running))
  rcases orElse_eq_some hrun with hf | hrun
  · exact logsPotential_le_of_logs (logs_storageStep hf h)
      (gasHeld_le_of_measure_lt (storageStep_measure_lt hf h running))
  rcases orElse_eq_some hrun with hf | hrun
  · exact logsPotential_le_of_logs (logs_transientStorageStep hf h)
      (gasHeld_le_of_measure_lt (transientStorageStep_measure_lt hf h running))
  rcases orElse_eq_some hrun with hf | hf
  · cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    exact logsPotential_logStep h
  · cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    exact logsPotential_selfdestructStep h

/-! ## The calls and the creations -/

/-- The price of sending value covers the stipend and the allowance of one transfer log. -/
theorem stipend_add_transferAllowance_le {value : U256} (h : value ≠ 0) :
    CALL_STIPEND + transferAllowance fork ≤ callValueCost fork value := by
  unfold callValueCost transferAllowance
  simp only [h, ↓reduceIte]
  split <;> simp [CALL_STIPEND, ACCOUNT_WRITE, CALL_VALUE]

/-- A call pays the gas it passes on, and the allowance of a transfer log when it sends value.

It keeps the logs. -/
theorem payCall_gasHeld [LawfulGasMeter Meter] {kind : CallKind} {call : CallOperands}
    {memoryCost extraGas newAccount subCall : Nat} {evm after : Evm fork Meter}
    (above : callValueCost fork call.value ≤ extraGas)
    (h : payCall kind call memoryCost extraGas newAccount evm = .ok (subCall, after)) :
    after.substate.logs = evm.substate.logs ∧
      GasMeter.gasHeld after.gas + subCall +
          (if call.value = 0 then 0 else transferAllowance fork) ≤
        GasMeter.gasHeld evm.gas := by
  unfold payCall at h
  split at h
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    refine ⟨(chargeGas_sameContext h3).logs.trans ((chargeStateGas_sameContext h2).logs.trans
      (chargeGas_sameContext h1).logs), ?_⟩
    have paid := (((chargeGas_pays h1).trans (chargeStateGas_pays h2)).trans
      (chargeGas_pays h3)).gasHeld
    rw [subCall_eq_cost_add_stipend]
    by_cases hv : call.value = 0
    · simp only [hv, ↓reduceIte] at paid ⊢
      omega
    · have := stipend_add_transferAllowance_le (fork := fork) hv
      simp only [hv, ↓reduceIte] at paid ⊢
      omega
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    cases h
    refine ⟨(chargeGas_sameContext h1).logs, ?_⟩
    have paid := (chargeGas_pays h1).gasHeld
    simp only [messageCallGas] at paid ⊢
    by_cases hv : call.value = 0
    · simp only [hv, ↓reduceIte] at paid ⊢
      omega
    · have := stipend_add_transferAllowance_le (fork := fork) hv
      simp only [hv, ↓reduceIte] at paid ⊢
      omega

/-- A caller that takes in a child has at most the weight of the logs of both. -/
theorem logsWeight_incorporateChild (caller child : Evm fork Meter) :
    logsWeight (incorporateChild fork caller child).substate.logs.toList ≤
      logsWeight caller.substate.logs.toList + logsWeight child.substate.logs.toList := by
  unfold incorporateChild
  dsimp only
  split
  · simp only [Array.toList_append, logsWeight_append]
    exact Nat.le_refl _
  · exact Nat.le_add_right _ _

/-- A caller that takes in a child has at most the potential of both. -/
theorem logsPotential_incorporateChild [LawfulGasMeter Meter] (caller child : Evm fork Meter) :
    logsPotential (incorporateChild fork caller child) ≤
      logsPotential caller + logsPotential child := by
  have g := gasHeld_incorporateChild (fork := fork) caller child
  have l := logsWeight_incorporateChild (fork := fork) caller child
  unfold logsPotential
  omega

/-- A refill of state gas raises no potential. -/
theorem logsPotential_refillStateGas [LawfulGasMeter Meter] (evm : Evm fork Meter) (n : Nat) :
    logsPotential (refillStateGas evm n) ≤ logsPotential evm :=
  logsPotential_le_of_logs rfl (LawfulGasMeter.gasHeld_refill _ _)

/-- A caller that resumes after a call has at most the potential of the caller and the child. -/
theorem logsPotential_resumeCall [LawfulGasMeter Meter] {caller child after : Evm fork Meter}
    {newAccount : Nat} {outputStart outputSize : U256}
    (h : resumeCall fork caller newAccount outputStart outputSize child = .ok after) :
    logsPotential after ≤ logsPotential caller + logsPotential child := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  refine Nat.le_trans (logsPotential_le_of_logs (pushWord_sameContext h1).logs
    (Nat.le_trans (Nat.le_add_right _ _) (pushWord_pays h1).gasHeld)) ?_
  refine Nat.le_trans ?_ (logsPotential_incorporateChild (fork := fork) caller child)
  split
  · exact Nat.le_refl _
  · exact logsPotential_refillStateGas (incorporateChild fork caller child) newAccount

/-- A creator that resumes after a creation has at most the potential of it and the child. -/
theorem logsPotential_resumeCreate [LawfulGasMeter Meter] {caller child after : Evm fork Meter}
    {newAccount : Nat} {address : Address}
    (h : resumeCreate fork caller newAccount address child = .ok after) :
    logsPotential after ≤ logsPotential caller + logsPotential child := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  refine Nat.le_trans (logsPotential_le_of_logs (pushWord_sameContext h1).logs
    (Nat.le_trans (Nat.le_add_right _ _) (pushWord_pays h1).gasHeld)) ?_
  refine Nat.le_trans ?_ (logsPotential_incorporateChild (fork := fork) caller child)
  split
  · exact Nat.le_refl _
  · exact logsPotential_refillStateGas (incorporateChild fork caller child) newAccount

/-- A call that runs no message keeps the logs, and gets back exactly its gas. -/
theorem logsPotential_skipCall [LawfulGasMeter Meter] {evm after : Evm fork Meter}
    {gas reservoir : Nat} (h : skipCall evm gas reservoir = .ok after) :
    logsPotential after = logsPotential evm + gas := by
  have g := (skipCall_gasHeld h).1
  obtain ⟨stack, -, rfl⟩ := skipCall_eq_ok h
  unfold logsPotential at *
  simp only [advance] at g ⊢
  omega

/-- The access to a delegate keeps the logs. -/
theorem logs_accessDelegation {evm after : Evm fork Meter} {address : Address} {known : Nat}
    {callee : Callee} (h : accessDelegation evm address known = .ok (callee, after)) :
    after.substate.logs = evm.substate.logs := by
  obtain ⟨code, -, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact logs_accessAddress _ _
  · cases h
    rfl

/-- A creation pays at least the allowance of one transfer log. -/
theorem transferAllowance_le_createBaseCost : transferAllowance fork ≤ createBaseCost fork := by
  unfold transferAllowance
  split
  · rename_i hg
    rw [createBaseCost_of_glamsterdam hg]
    omega
  · omega

end EthLib.Execution.Evm
