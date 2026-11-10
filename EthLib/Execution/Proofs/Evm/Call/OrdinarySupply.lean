module

public import EthLib.Execution.Proofs.Evm.Call.Supply

/-!
# Proofs: instructions other than SELFDESTRUCT preserve ether supply

Storage, transient storage, logs and nonce changes preserve balances.

A call or creation moves its value only when its child enters, after the instruction's prelude.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

omit [GasMeter Meter] in
private theorem supply_of_static {a b : Evm fork Meter} (h : StaticStep a b) :
    b.state.supply = a.state.supply := TransactionState.supply_eq_of_sameOutside h.state

private theorem supply_sstoreStep {evm after : Evm fork Meter}
    (h : sstoreStep evm = .ok after) : after.state.supply = evm.state.supply := by
  unfold sstoreStep at h
  split at h
  · cases h
  obtain ⟨⟨k, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨n, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  have c2 : StaticStep evm e2 :=
    .of_sameContext ((popWord_sameContext h1).trans (popWord_sameContext h2))
  dsimp only at h
  split at h
  · cases h
  · rcases pair : accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k) with
      ⟨cold, e3⟩
    have pre : StaticStep evm (recordStorageRead e3 e2.message.currentTarget k.toBeBytes) := by
      have accessed := staticStep_accessStorageKey e2 e2.message.currentTarget k.toBeBytes
      rw [pair] at accessed
      exact (c2.trans accessed).trans (staticStep_recordStorageRead _ _ _)
    simp only [pair] at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
      have pre5 : StaticStep evm e5 :=
        pre.trans (.of_sameContext ((sameContext_refillStateGas _ _).trans
          ((chargeGas_sameContext h4).trans (chargeStateGas_sameContext h5))))
      split at h
      · cases h
      · obtain ⟨st, written, h⟩ := Base.bind_ok_iff.mp h
        cases h
        exact (TransactionState.supply_setStorage (Base.mapError_ok_iff.mp written)).trans
          (supply_of_static pre5)
    · exact supply_of_static (pre.trans (staticStep_exceptionalHalt _ _))

private theorem supply_tstoreStep {evm after : Evm fork Meter}
    (h : tstoreStep evm = .ok after) : after.state.supply = evm.state.supply := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · cases h
  · cases h
    change e3.state.supply = evm.state.supply
    exact supply_of_static (.of_sameContext ((popWord_sameContext h1).trans
      ((popWord_sameContext h2).trans (chargeGas_sameContext h3))))

/-- An ordinary instruction preserves the supply unless its opcode is SELFDESTRUCT. -/
theorem instruction_supply_eq_of_ne_selfdestruct {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (ordinary : op ≠ .selfdestruct) (selected : instruction fork op = some run)
    (ok : run evm = .ok after) : after.state.supply = evm.state.supply := by
  unfold instruction at selected
  rcases orElse_eq_some selected with hf | selected
  · rw [(stackOnlyStep_sameContext hf ok).state]
  rcases orElse_eq_some selected with hf | selected
  · rw [(controlFlowStep_sameContext hf ok).state]
  rcases orElse_eq_some selected with hf | selected
  · rw [(memoryDataStep_sameContext hf ok).state]
  rcases orElse_eq_some selected with hf | selected
  · exact supply_of_static (staticStep_returnOpStep hf ok)
  rcases orElse_eq_some selected with hf | selected
  · rw [(environmentStep_sameContext hf ok).state]
  rcases orElse_eq_some selected with hf | selected
  · exact supply_of_static (staticStep_accountStep hf ok)
  rcases orElse_eq_some selected with hf | selected
  · cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hf
    case sload => subst hf; exact supply_of_static (staticStep_sloadStep ok)
    case sstore => subst hf; exact supply_sstoreStep ok
  rcases orElse_eq_some selected with hf | selected
  · cases op <;> simp only [transientStorageStep, reduceCtorEq] at hf <;> split at hf <;>
      simp only [Option.some.injEq, reduceCtorEq] at hf <;> subst hf
    · rw [(tloadStep_sameContext ok).state]
    · exact supply_tstoreStep ok
  rcases orElse_eq_some selected with hf | hf
  · cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    obtain ⟨_, -, -, -, -, state, -⟩ := logStep_eq_ok ok
    rw [state]
  · cases op <;> simp_all only [selfdestructOpStep, reduceCtorEq, ne_eq, not_true_eq_false]

/-- The supply of the next frame or the caller before its child runs. -/
def StepResult.headSupply : StepResult fork Meter → Nat
  | .next evm | .child evm _ _ => evm.state.supply

omit [GasMeter Meter] in
private theorem headSupply_trans {a b : Evm fork Meter} {result : StepResult fork Meter}
    (before : b.state.supply = a.state.supply)
    (head : result.headSupply = b.state.supply) : result.headSupply = a.state.supply :=
  head.trans before

private theorem headSupply_genericCall {evm : Evm fork Meter} {message : Message fork}
    {newAccount : Nat} {outputStart outputSize : U256} {result : StepResult fork Meter}
    (h : genericCall evm message newAccount outputStart outputSize = .ok result) :
    result.headSupply = evm.state.supply := by
  unfold genericCall at h
  dsimp only at h
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact supply_of_static (((StaticStep.of_sameContext
      (sameContext_returnData evm .empty)).trans
      (.of_sameContext (sameContext_refillStateGas _ newAccount))).trans
      (staticStep_skipCall hs))
  · cases h
    rfl

private theorem headSupply_finishCall {kind : CallKind} {call : CallOperands}
    {callee : Callee} {subCall newAccount expandBy : Nat} {evm : Evm fork Meter}
    {result : StepResult fork Meter}
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    result.headSupply = evm.state.supply := by
  unfold finishCall at h
  split at h
  · cases h
  dsimp only at h
  have pre : StaticStep evm (recordAccountRead { evm with
      memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
      evm.message.currentTarget) := ⟨StateKept.refl _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact supply_of_static ((pre.trans (.of_sameContext
      (sameContext_refillStateGas _ _))).trans (staticStep_skipCall hs))
  · exact headSupply_trans (supply_of_static pre) (headSupply_genericCall h)

private theorem headSupply_callStep {kind : CallKind} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : callStep kind evm = .ok result) :
    result.headSupply = evm.state.supply := by
  unfold callStep at h
  obtain ⟨⟨call, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  have c1 := (staticStep_popCallOperands h1).1
  dsimp only at h
  split at h
  · cases h
  rcases pair : accessAddress e1 call.address with ⟨cold, e2⟩
  simp only [pair] at h
  have accessed := staticStep_accessAddress e1 call.address
  rw [pair] at accessed
  have s3 := (c1.trans accessed).trans (staticStep_recordAccountRead e2 call.address)
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨⟨callee, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
    have s4 := s3.trans (staticStep_accessDelegation h4)
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨⟨subCall, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
      exact headSupply_trans (supply_of_static (s4.trans (staticStep_payCall h5)))
        (headSupply_finishCall h)
    · exact supply_of_static (s4.trans (staticStep_exceptionalHalt _ _))
  · exact supply_of_static (s3.trans (staticStep_exceptionalHalt _ _))

private theorem headSupply_launchCreate {evm : Evm fork Meter} {value : U256}
    {initCode : ByteArray} {salt : Option U256} {result : StepResult fork Meter}
    (h : launchCreate evm value initCode salt = .ok result) :
    result.headSupply = evm.state.supply := by
  unfold launchCreate at h
  dsimp only at h
  have pre : StaticStep evm
      (recordAccountRead { evm with returnData := .empty } evm.message.currentTarget) :=
    (StaticStep.of_sameContext (sameContext_returnData evm .empty)).trans
      (staticStep_recordAccountRead _ _)
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact supply_of_static (pre.trans (staticStep_skipCall hs))
  obtain ⟨address, -, h⟩ := Base.bind_ok_iff.mp h
  have c0 := (pre.trans (staticStep_accessAddress _ address)).trans
    (staticStep_recordAccountRead _ address)
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨state, written, h⟩ := Base.bind_ok_iff.mp h
    have before : e2.state.supply = evm.state.supply :=
      supply_of_static (c0.trans (.of_sameContext
        ((chargeStateGas_sameContext h1).trans (chargeGas_sameContext h2))))
    have stateSupply := (TransactionState.supply_incrementNonce
      (Base.mapError_ok_iff.mp written)).trans before
    split at h
    · cases h
      exact stateSupply
    · obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
      cases h
      exact (congrArg TransactionState.supply (pushWord_sameContext h3).state).trans stateSupply
  · exact supply_of_static (c0.trans (staticStep_exceptionalHalt _ _))

private theorem headSupply_createStep {create2 : Bool} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : createStep create2 evm = .ok result) :
    result.headSupply = evm.state.supply := by
  unfold createStep at h
  by_cases static : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp [static, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  rw [ite_eq_right_of_eq_false _ _ (eq_false static)] at h
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨salt, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
  have m4 : SameContext e3 e4 := by
    unfold popSalt at h4
    split at h4
    · obtain ⟨⟨_, e⟩, he, h4⟩ := Base.bind_ok_iff.mp h4
      cases h4
      exact popWord_sameContext he
    · cases h4
      exact SameContext.refl _
  have before : e5.state.supply = evm.state.supply :=
    supply_of_static (.of_sameContext (((((popWord_sameContext h1).trans
      (popWord_sameContext h2)).trans (popWord_sameContext h3)).trans m4).trans
      (chargeGasAndMemory_sameContext h5)))
  unfold genericCreate at h
  split at h
  · cases h
  split at h
  · cases h
  exact headSupply_trans before (headSupply_launchCreate h)

/-- A message instruction preserves supply before the child runs, including skipped messages. -/
theorem messageInstruction_head_supply {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (selected : messageInstruction fork op = some run)
    (ok : run evm = .ok result) : result.headSupply = evm.state.supply := by
  unfold messageInstruction at selected
  cases call : callInstruction (Meter := Meter) fork op with
  | some f =>
    simp only [call, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at selected
    subst selected
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at call
    all_goals first
      | (subst call; exact headSupply_callStep ok)
      | (split at call
         · simp only [Option.some.injEq] at call
           subst call
           exact headSupply_callStep ok
         · cases call)
  | none =>
    simp only [call, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at selected
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at selected
    all_goals first
      | (subst selected; exact headSupply_createStep ok)
      | (split at selected
         · simp only [Option.some.injEq] at selected
           subst selected
           exact headSupply_createStep ok
         · cases selected)

end EthLib.Execution.Evm
