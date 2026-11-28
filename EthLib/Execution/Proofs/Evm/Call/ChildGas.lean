module

public import EthLib.Execution.Proofs.Evm.Call.StepRules
public import EthLib.Execution.Proofs.Evm.Gas.CallGas

/-!
# Proofs: the gas of a message is at most all but one 64th of its frame's gas, less 100

From Berlin, a call or a creation pays at least 100 gas before it sends its message.

It then passes on at most all but one 64th of what is left, by [EIP-150][eip150].

The stipend of a call with value is less than the price of the value, so it adds no more.

[eip150]: https://eips.ethereum.org/EIPS/eip-150#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]

omit [LawfulGasMeter Meter] in
/-- A call that sends a message sends it one level below its caller. -/
theorem callStep_child_depth {kind : CallKind} {evm caller : Evm fork Meter}
    {message : Message fork} {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : callStep kind evm = .ok (.child caller message resume)) :
    message.depth = caller.message.depth + 1 := by
  unfold Evm.callStep at h
  obtain ⟨⟨call, e1⟩, -, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h; cases h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨_, hc⟩
  · obtain ⟨⟨callee, e4⟩, -, h⟩ := Base.bind_ok_iff.mp h
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨_, hc⟩
    · obtain ⟨⟨subCall, e5⟩, -, h⟩ := Base.bind_ok_iff.mp h
      unfold Evm.finishCall at h
      split at h
      · cases h
      dsimp only at h
      split at h
      · obtain ⟨_, -, hc⟩ := Base.map_ok_iff.mp h; cases hc
      · unfold Evm.genericCall at h
        split at h
        · obtain ⟨_, -, hc⟩ := Base.map_ok_iff.mp h; cases hc
        · cases h; rfl
    · cases hc
  · cases hc

omit [LawfulGasMeter Meter] in
/-- A creation that sends a message sends it one level below its caller. -/
theorem createStep_child_depth {create2 : Bool} {evm caller : Evm fork Meter}
    {message : Message fork} {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : createStep create2 evm = .ok (.child caller message resume)) :
    message.depth = caller.message.depth + 1 := by
  obtain ⟨_, _, _, _, _, _, -, -, -, -, -, h⟩ := createStep_eq_ok h
  unfold Evm.launchCreate at h
  dsimp only at h
  split at h
  · obtain ⟨_, -, hc⟩ := Base.map_ok_iff.mp h; cases hc
  obtain ⟨address, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨_, hc⟩
  · obtain ⟨e1, -, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e2, -, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨state, -, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · cases h; rfl
    · obtain ⟨_, -, hc⟩ := Base.bind_ok_iff.mp h; cases hc
  · cases hc

omit [LawfulGasMeter Meter] in
/-- A step that sends a message runs a call instruction or a creation on its frame. -/
private theorem step_eq_child_cases {evm caller : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : step fork evm = .ok (.child caller message resume)) :
    (∃ kind, callStep kind evm = .ok (.child caller message resume)) ∨
      ∃ create2, createStep create2 evm = .ok (.child caller message resume) := by
  unfold Evm.step at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · obtain ⟨_, -, hc⟩ := Base.map_ok_iff.mp h; cases hc
      · split at h
        · rename_i hrun
          unfold Evm.messageInstruction at hrun
          rcases orElse_eq_some hrun with hc | hc
          · cases ‹Op› <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
            all_goals (try split at hc) <;>
              (try simp only [Option.some.injEq, reduceCtorEq] at hc) <;> (try subst hc)
            all_goals first
              | cases hc
              | exact .inl ⟨_, h⟩
          · cases ‹Op› <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hc
            all_goals (try split at hc) <;>
              (try simp only [Option.some.injEq, reduceCtorEq] at hc) <;> (try subst hc)
            all_goals first
              | cases hc
              | exact .inr ⟨_, h⟩
        · cases h
  · obtain ⟨_, -, hc⟩ := Base.map_ok_iff.mp h; cases hc

/-- A message of all but one 64th of what is left after a price of at least 100 fits the bound.

A stipend fits too when the price is at least 9100. -/
private theorem maxMessageCallGas_add_le {x cost held stipend : Nat} (le : x + cost ≤ held)
    (base : 100 ≤ cost) (stip : stipend = 0 ∨ stipend = CALL_STIPEND ∧ 9100 ≤ cost) :
    100 ≤ held ∧ maxMessageCallGas x + stipend ≤ maxMessageCallGas (held - 100) := by
  unfold maxMessageCallGas CALL_STIPEND at *
  omega

omit [LawfulGasMeter Meter] in
/-- A charge that succeeds was within the execution gas left, when the meter charges so. -/
private theorem le_gasLeft_of_chargeGas
    (charge : ∀ {meter after : Meter} {amount : Nat}, GasMeter.charge meter amount = .ok after →
      amount ≤ GasMeter.gasLeft meter)
    {evm after : Evm fork Meter} {amount : Nat} (h : chargeGas evm amount = .ok after) :
    amount ≤ GasMeter.gasLeft evm.gas := by
  obtain ⟨_, hc, -⟩ := Base.bind_ok_iff.mp h
  exact charge hc

/-- From Tangerine Whistle, a call passes on all but one 64th of what is left after its price.

The stipend of a call with value comes on top. -/
private theorem payCall_subCall_le (hfork : fork ≥ .tangerineWhistle)
    (charge : ∀ {meter after : Meter} {amount : Nat}, GasMeter.charge meter amount = .ok after →
      amount ≤ GasMeter.gasLeft meter)
    {kind : CallKind} {call : CallOperands} {memoryCost extraGas newAccount subCall : Nat}
    {evm after : Evm fork Meter}
    (h : payCall kind call memoryCost extraGas newAccount evm = .ok (subCall, after)) :
    ∃ x, x + extraGas ≤ GasMeter.gasHeld evm.gas ∧
      subCall ≤ maxMessageCallGas x + if call.value = 0 then 0 else CALL_STIPEND := by
  unfold payCall at h
  split at h
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have paid := (chargeGas_pays h1).trans (chargeStateGas_pays h2)
    have := paid.gasHeld
    have := LawfulGasMeter.gasLeft_le_gasHeld e2.gas
    refine ⟨GasMeter.gasLeft e2.gas, by omega, ?_⟩
    rw [messageCallGas_of_le hfork (Nat.zero_le _)]
    dsimp only
    have := Nat.min_le_right call.gas.toNat (maxMessageCallGas (GasMeter.gasLeft e2.gas - 0 - 0))
    simp only [Nat.sub_zero] at this ⊢
    omega
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have le := le_gasLeft_of_chargeGas charge h1
    have := LawfulGasMeter.gasLeft_le_gasHeld evm.gas
    have enough : extraGas + memoryCost ≤ GasMeter.gasLeft evm.gas := by
      have : extraGas ≤ (messageCallGas fork call.value call.gas.toNat (GasMeter.gasLeft evm.gas)
          memoryCost extraGas).cost := by
        unfold messageCallGas
        dsimp only
        omega
      omega
    refine ⟨GasMeter.gasLeft evm.gas - memoryCost - extraGas, by omega, ?_⟩
    rw [messageCallGas_of_le hfork enough]
    dsimp only
    have := Nat.min_le_right call.gas.toNat
      (maxMessageCallGas (GasMeter.gasLeft evm.gas - memoryCost - extraGas))
    omega

omit [LawfulGasMeter Meter] in
/-- The end of a call that sends a message passes on the gas the call paid for. -/
private theorem finishCall_child_gas {kind : CallKind} {call : CallOperands} {callee : Callee}
    {subCall newAccount expandBy : Nat} {evm caller : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : finishCall kind call callee subCall newAccount expandBy evm =
      .ok (.child caller message resume)) : message.gas = subCall := by
  unfold Evm.finishCall at h
  split at h
  · cases h
  dsimp only at h
  split at h
  · obtain ⟨_, -, hc⟩ := Base.map_ok_iff.mp h; cases hc
  · unfold Evm.genericCall at h
    split at h
    · obtain ⟨_, -, hc⟩ := Base.map_ok_iff.mp h; cases hc
    · cases h; rfl

/-- From Berlin, the extra price of a call is at least 100, and at least 9100 with value. -/
private theorem callExtraGas_ge (hfork : .berlin ≤ fork) {kind : CallKind}
    {state : State.TransactionState} {call : CallOperands} {cold : Bool} {callee : Callee} :
    100 ≤ callExtraGas fork kind state call cold callee ∧
      (call.value ≠ 0 → 9100 ≤ callExtraGas fork kind state call cold callee) := by
  have base : 100 ≤ callBaseCost fork cold := by
    unfold callBaseCost accountAccessCost
    simp only [ge_iff_le, hfork, ite_true]
    split
    · dsimp only [gasSchedule]
      repeat' split
      all_goals decide
    · decide
  have value : call.value ≠ 0 → 9000 ≤ callValueCost fork call.value := by
    intro hv
    unfold callValueCost
    simp only [hv, ite_false]
    split <;> decide
  unfold callExtraGas
  dsimp only
  exact ⟨by omega, fun hv => by have := value hv; omega⟩

/-- From Berlin, a call that sends a message holds at least 100 gas.

Its message gets at most all but one 64th of that gas, less 100. -/
private theorem callStep_child_gas (hfork : .berlin ≤ fork)
    (charge : ∀ {meter after : Meter} {amount : Nat}, GasMeter.charge meter amount = .ok after →
      amount ≤ GasMeter.gasLeft meter)
    {kind : CallKind} {evm caller : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : callStep kind evm = .ok (.child caller message resume)) :
    100 ≤ GasMeter.gasHeld evm.gas ∧
      message.gas ≤ maxMessageCallGas (GasMeter.gasHeld evm.gas - 100) := by
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
  rcases keepReads_eq_ok h with h | ⟨_, hc⟩
  · obtain ⟨⟨callee, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
    rcases keepReads_eq_ok h with h | ⟨_, hc⟩
    · obtain ⟨⟨subCall, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
      dsimp only at h4
      have paid := (((popCallOperands_pays h1).trans p2).trans
        (recordAccountRead_pays _ call.address)).trans (accessDelegation_pays h3)
      have := paid.gasHeld
      rw [finishCall_child_gas h]
      obtain ⟨x, hx, hs⟩ :=
        payCall_subCall_le (Nat.le_trans (by decide : Fork.tangerineWhistle ≤ .berlin) hfork)
          charge h4
      obtain ⟨base, value⟩ := callExtraGas_ge hfork (kind := kind) (state := e3.state)
        (call := call) (cold := cold) (callee := callee)
      have bound := maxMessageCallGas_add_le (x := x) (held := GasMeter.gasHeld evm.gas)
        (stipend := if call.value = 0 then 0 else CALL_STIPEND) (by omega) base (by
          by_cases hv : call.value = 0
          · simp [hv]
          · exact .inr ⟨ite_eq_right_of_eq_false _ _ (eq_false hv), value hv⟩)
      exact ⟨bound.1, by omega⟩
    · cases hc
  · cases hc

/-- From Berlin, a creation that sends a message holds at least 100 gas.

Its message gets at most all but one 64th of that gas, less 100. -/
private theorem createStep_child_gas (hfork : .berlin ≤ fork) {create2 : Bool}
    {evm caller : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : createStep create2 evm = .ok (.child caller message resume)) :
    100 ≤ GasMeter.gasHeld evm.gas ∧
      message.gas ≤ maxMessageCallGas (GasMeter.gasHeld evm.gas - 100) := by
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
  have paid := (((((popWord_pays h1).trans (popWord_pays h2)).trans (popWord_pays h3)).trans
    (popSalt_pays h4)).trans (chargeGasAndMemory_pays h5)).mono (m := createBaseCost fork)
    (by omega)
  have base : 100 ≤ createBaseCost fork := by
    unfold createBaseCost
    dsimp only [gasSchedule]
    repeat' split
    all_goals decide
  unfold genericCreate at h
  split at h
  · cases h
  split at h
  · cases h
  unfold launchCreate at h
  dsimp only at h
  have start : Pays (createBaseCost fork) evm
      (recordAccountRead { e5 with returnData := .empty } e5.message.currentTarget) :=
    paid.congr rfl rfl
  split at h
  · obtain ⟨_, -, hc⟩ := Base.map_ok_iff.mp h; cases hc
  obtain ⟨address, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨_, hc⟩
  · obtain ⟨e6, h6, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e7, -, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨state, -, h⟩ := Base.bind_ok_iff.mp h
    have access := (accessAddress_pays
      (recordAccountRead { e5 with returnData := .empty } e5.message.currentTarget)
      address).trans (recordAccountRead_pays _ address)
    have p6 := ((start.trans access).trans (chargeStateGas_pays h6)).gasHeld
    have := LawfulGasMeter.gasLeft_le_gasHeld e6.gas
    split at h
    · cases h
      have bound := maxMessageCallGas_add_le (x := GasMeter.gasLeft e6.gas)
        (held := GasMeter.gasHeld evm.gas) (stipend := 0) (by omega) base (.inl rfl)
      refine ⟨bound.1, ?_⟩
      show createMessageGas fork (GasMeter.gasLeft e6.gas) ≤ _
      have tw : fork ≥ .tangerineWhistle :=
        Nat.le_trans (by decide : Fork.tangerineWhistle ≤ .berlin) hfork
      simp only [createMessageGas, tw, ite_true]
      omega
    · obtain ⟨_, -, hc⟩ := Base.bind_ok_iff.mp h; cases hc
  · cases hc

/-- From Berlin, a step that sends a message holds at least 100 gas.

Its message gets at most all but one 64th of the gas the step holds, less 100.

The meter must charge execution gas only within the execution gas left, as each meter does. -/
theorem gas_le_of_step_eq_child (hfork : .berlin ≤ fork)
    (charge : ∀ {meter after : Meter} {amount : Nat}, GasMeter.charge meter amount = .ok after →
      amount ≤ GasMeter.gasLeft meter)
    {evm caller : Evm fork Meter}
    {message : Message fork} {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : step fork evm = .ok (.child caller message resume)) :
    100 ≤ GasMeter.gasHeld evm.gas ∧
      message.gas ≤ maxMessageCallGas (GasMeter.gasHeld evm.gas - 100) := by
  rcases step_eq_child_cases h with ⟨_, h⟩ | ⟨_, h⟩
  · exact callStep_child_gas hfork charge h
  · exact createStep_child_gas hfork h

omit [LawfulGasMeter Meter] in
/-- A step that sends a message sends it one level below its frame. -/
theorem depth_of_step_eq_child {evm caller : Evm fork Meter}
    {message : Message fork} {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : step fork evm = .ok (.child caller message resume)) :
    message.depth = evm.message.depth + 1 := by
  rw [← (stepRules_messageCode.step h).1.1]
  rcases step_eq_child_cases h with ⟨_, h⟩ | ⟨_, h⟩
  · exact callStep_child_depth h
  · exact createStep_child_depth h

/-- The meter before Glamsterdam charges only within the gas left. -/
theorem charge_le_gasLeft_nat {meter after : Nat} {amount : Nat}
    (h : GasMeter.charge meter amount = .ok after) : amount ≤ GasMeter.gasLeft meter := by
  simp only [GasMeter.charge] at h
  split at h
  · cases h
  · simp only [GasMeter.gasLeft]
    omega

/-- The meter of Glamsterdam charges execution gas only within the execution gas left. -/
theorem charge_le_gasLeft_stateGas {meter after : StateGasMeter} {amount : Nat}
    (h : GasMeter.charge meter amount = .ok after) : amount ≤ GasMeter.gasLeft meter := by
  simp only [GasMeter.charge, StateGasMeter.charge] at h
  split at h
  · cases h
  · simp only [GasMeter.gasLeft]
    omega

end EthLib.Execution.Evm
