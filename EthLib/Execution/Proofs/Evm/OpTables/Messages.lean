module

public import EthLib.Execution.Proofs.Evm.OpTables.Parts
public import EthLib.Execution.Proofs.Evm.Gas.Prices
public import EthLib.Execution.Proofs.Evm.Call.Reads
public import EthLib.Base.Proofs.Except

/-!
# Proofs: the calls and the creations follow the tables

A call or a creation takes its words and pays its constant price before it sends its message.

The frame that resumes pushes one word, and keeps the code.

A call or a creation that sends no message pushes that word at once.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]

/-! ## The frame that resumes -/

omit [LawfulGasMeter Meter] in
/-- A caller that takes in its child keeps its stack, its code and its destinations. -/
theorem incorporateChild_code_stack (caller child : Evm fork Meter) :
    (incorporateChild fork caller child).stack = caller.stack ∧
      (incorporateChild fork caller child).code = caller.code ∧
      (incorporateChild fork caller child).validJumpDestinations =
        caller.validJumpDestinations := by
  unfold incorporateChild
  split <;> exact ⟨rfl, rfl, rfl⟩

omit [LawfulGasMeter Meter] in
/-- A caller that resumes after a call pushes one word and keeps its code. -/
theorem resumeCall_code_stack {caller child after : Evm fork Meter} {newAccount : Nat}
    {outputStart outputSize : U256}
    (h : resumeCall fork caller newAccount outputStart outputSize child = .ok after) :
    after.code = caller.code ∧ after.validJumpDestinations = caller.validJumpDestinations ∧
      after.stack.val.length = caller.stack.val.length + 1 := by
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have m := pushWord_moves h1
  obtain ⟨hs, hc, hj⟩ := incorporateChild_code_stack caller child
  have mc := m.code
  have mj := m.jumps
  have ms := m.stack
  dsimp only at mc mj ms
  refine ⟨mc.trans ?_, mj.trans ?_, ?_⟩
  · split <;> exact hc
  · split <;> exact hj
  · show e.stack.val.length = _
    split at ms <;> simp only [refillStateGas, hs] at ms <;> omega

omit [LawfulGasMeter Meter] in
/-- A creator that resumes after a creation pushes one word and keeps its code. -/
theorem resumeCreate_code_stack {caller child after : Evm fork Meter} {newAccount : Nat}
    {address : Address} (h : resumeCreate fork caller newAccount address child = .ok after) :
    after.code = caller.code ∧ after.validJumpDestinations = caller.validJumpDestinations ∧
      after.stack.val.length = caller.stack.val.length + 1 := by
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have m := pushWord_moves h1
  obtain ⟨hs, hc, hj⟩ := incorporateChild_code_stack caller child
  have mc := m.code
  have mj := m.jumps
  have ms := m.stack
  dsimp only at mc mj ms
  refine ⟨mc.trans ?_, mj.trans ?_, ?_⟩
  · split <;> exact hc
  · split <;> exact hj
  · show e.stack.val.length = _
    split at ms <;> simp only [refillStateGas, hs] at ms <;> omega

omit [LawfulGasMeter Meter] in
/-- A caller that has paid and resumes with one more word follows the tables. -/
theorem followsTablesChild_of_moves {before caller : Evm fork Meter} {takes price : Nat}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : Moves takes 0 price before caller) (pos : 1 ≤ takes)
    (hres : ∀ child after, resume child = .ok after →
      after.code = caller.code ∧ after.validJumpDestinations = caller.validJumpDestinations ∧
        after.stack.val.length = caller.stack.val.length + 1) :
    FollowsTablesChild takes 1 price before caller resume := by
  have := h.stack
  have := before.stack.property
  exact ⟨by omega, by omega, h.gas, h.code, h.jumps, hres⟩

/-- A frame that gets back the gas of a message it never sent, and pushes a word. -/
theorem skipCall_moves {before evm after : Evm fork Meter} {takes gas reservoir price : Nat}
    (h : Moves takes 0 (gas + price) before evm) (hs : skipCall evm gas reservoir = .ok after) :
    Moves takes 1 price before after := by
  obtain ⟨g, hg⟩ := skipCall_gasHeld hs
  obtain ⟨_, h1, h2⟩ := Base.bind_ok_iff.mp hs
  cases h2
  have m := pushWord_moves h1
  have := h.gas
  have := h.stack
  have := m.stack
  exact ⟨h.enough, by simp only [advance] at *; omega, by omega, m.code.trans h.code,
    m.jumps.trans h.jumps⟩

/-! ## The calls -/

omit [LawfulGasMeter Meter] in
/-- The pops of the operands of a call take seven words, or six without a value. -/
theorem popCallOperands_moves {kind : CallKind} {evm after : Evm fork Meter}
    {call : CallOperands} (h : popCallOperands kind evm = .ok (call, after)) :
    Moves (if kind.sendsValue then 7 else 6) 0 0 evm after := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e6⟩, h6, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e7⟩, h7, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have p3 : Moves (if kind.sendsValue then 1 else 0) 0 0 e2 e3 := by
    unfold popCallValue at h3
    split at h3
    · rename_i hv
      simpa [hv] using popWord_moves h3
    · rename_i hv
      cases h3
      simpa [hv] using Moves.refl e2
  have m := (((((((popWord_moves h1).trans (popWord_moves h2)).trans p3).trans
    (popWord_moves h4)).trans (popWord_moves h5)).trans (popWord_moves h6)).trans
    (popWord_moves h7))
  exact m.weaken (hp := Nat.zero_le _) (ht := by split <;> simp) (hl := by split <;> simp)

omit [LawfulGasMeter Meter] in
/-- The access to a delegate moves nothing. -/
theorem accessDelegation_moves {evm after : Evm fork Meter} {address : Address} {known : Nat}
    {callee : Callee} (h : accessDelegation evm address known = .ok (callee, after)) :
    Moves 0 0 0 evm after := by
  obtain ⟨code, -, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact ((accessAddress_moves _ _).trans (recordAccountRead_moves _ _)).weaken
  · cases h
    exact .refl _

/-- A call pays at least the gas it passes on and its extra price, less the stipend. -/
theorem payCall_moves {kind : CallKind} {call : CallOperands}
    {memoryCost extraGas newAccount subCall : Nat} {evm after : Evm fork Meter}
    (above : call.value ≠ 0 → CALL_STIPEND < extraGas)
    (h : payCall kind call memoryCost extraGas newAccount evm = .ok (subCall, after)) :
    Moves 0 0 (subCall + (extraGas - (if call.value = 0 then 0 else CALL_STIPEND))) evm after := by
  unfold payCall at h
  split at h
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    refine (((chargeGas_moves h1).trans (chargeStateGas_moves h2)).trans
      (chargeGas_moves h3)).weaken (hp := ?_)
    rw [subCall_eq_cost_add_stipend]
    split
    · omega
    · have := above ‹_›
      omega
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    cases h
    refine (chargeGas_moves h1).weaken (hp := ?_)
    unfold messageCallGas
    dsimp only
    by_cases hv : call.value = 0
    · simp only [hv, ↓reduceIte]
      omega
    · have := above hv
      simp only [hv, ↓reduceIte]
      omega

/-- The extra price of a call, less its stipend, is at least the warm price of the call. -/
theorem callBaseCost_le_callExtraGas {kind : CallKind} {state : State.TransactionState}
    {call : CallOperands} {cold : Bool} {callee : Callee} :
    callBaseCost fork false + (if call.value = 0 then 0 else CALL_STIPEND) ≤
      callExtraGas fork kind state call cold callee := by
  have := callBaseCost_le fork cold
  unfold callExtraGas
  dsimp only
  split
  · omega
  · have := stipend_lt_callValueCost (fork := fork) ‹_›
    omega

/-- The calling frame of a call moves nothing. -/
theorem callerFrame_moves (evm : Evm fork Meter) (expandBy : Nat) :
    Moves 0 0 0 evm (callerFrame evm expandBy) :=
  ⟨Nat.zero_le _, rfl, by simp [callerFrame, recordAccountRead, LawfulGasMeter.gasHeld_drain],
    rfl, rfl⟩

/-- The end of a call that has taken its words and paid follows the tables. -/
theorem finishCall_follows {kind : CallKind} {call : CallOperands} {callee : Callee}
    {subCall newAccount expandBy takes : Nat} {before evm : Evm fork Meter}
    {result : StepResult fork Meter} (paid : Moves takes 0 (subCall + callBaseCost fork false)
      before evm) (pos : 1 ≤ takes)
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    result.FollowsTables takes 1 (callBaseCost fork false) before := by
  unfold finishCall at h
  split at h
  · cases h
  dsimp only at h
  have caller := (paid.trans (callerFrame_moves evm expandBy)).weaken (t' := takes) (l' := 0)
    (p' := subCall + callBaseCost fork false)
  have skip : ∀ {after}, skipCall (refillStateGas (callerFrame evm expandBy) newAccount) subCall
      (GasMeter.reservoir evm.gas) = .ok after →
      StepResult.FollowsTables takes 1 (callBaseCost fork false) before (.next after) :=
    fun hs => (skipCall_moves ((caller.trans (refillStateGas_moves _ _)).weaken) hs).toFollows
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact skip hs
  · unfold genericCall at h
    split at h
    · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
      exact skip hs
    · cases h
      exact followsTablesChild_of_moves caller.weaken pos fun _ _ hr => resumeCall_code_stack hr

/-- A call takes its words and pays at least its price, or halts once it has read the state. -/
theorem callStep_follows {kind : CallKind} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : callStep kind evm = .ok result) :
    result.FollowsTables (if kind.sendsValue then 7 else 6) 1 (callBaseCost fork false) evm := by
  obtain ⟨⟨call, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  have m1 := popCallOperands_moves h1
  have pos : 1 ≤ if kind.sendsValue then 7 else 6 := by split <;> omega
  dsimp only at h
  split at h
  · cases h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  have m2 : Moves 0 0 0 e1 e2 := by
    have := accessAddress_moves e1 call.address
    rwa [hacc] at this
  rw [hacc] at h
  dsimp only at h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  have pre := (m1.trans m2).trans (recordAccountRead_moves e2 call.address)
  rcases keepReads_eq_ok_halt h with h | ⟨e, -, he, rfl⟩
  · obtain ⟨⟨callee, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
    have pre3 := pre.trans (accessDelegation_moves h3)
    rcases keepReads_eq_ok_halt h with h | ⟨e, -, he, rfl⟩
    · obtain ⟨⟨subCall, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
      have bounds := callBaseCost_le_callExtraGas (fork := fork) (kind := kind)
        (state := e3.state) (call := call) (cold := cold) (callee := callee)
      have above :
          call.value ≠ 0 → CALL_STIPEND < callExtraGas fork kind e3.state call cold callee :=
        fun hv => (callExtraGas_bounds (fork := fork)).2 hv
      have m4 := payCall_moves above h4
      exact finishCall_follows ((pre3.trans m4).weaken (hp := by
        have : (if call.value = 0 then 0 else CALL_STIPEND) ≤
            callExtraGas fork kind e3.state call cold callee := by
          omega
        omega)) pos h
    · exact FollowsTables.halt pre3 (by omega) he
  · exact FollowsTables.halt pre (by omega) he

/-! ## The creations -/

omit [LawfulGasMeter Meter] in
/-- The pop of the salt takes one word for CREATE2, and none for CREATE. -/
theorem popSalt_moves {create2 : Bool} {evm after : Evm fork Meter} {salt : Option U256}
    (h : popSalt create2 evm = .ok (salt, after)) :
    Moves (if create2 then 1 else 0) 0 0 evm after := by
  unfold popSalt at h
  cases create2
  · cases h
    exact .refl _
  · obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact popWord_moves h1

/-- The launch of a creation that has taken its words and paid follows the tables. -/
theorem launchCreate_follows {before evm : Evm fork Meter} {value : U256} {initCode : ByteArray}
    {salt : Option U256} {takes price : Nat} {result : StepResult fork Meter}
    (paid : Moves takes 0 price before evm) (pos : 1 ≤ takes)
    (h : launchCreate evm value initCode salt = .ok result) :
    result.FollowsTables takes 1 price before := by
  unfold launchCreate at h
  dsimp only at h
  have pre : Moves takes 0 price before
      (recordAccountRead { evm with returnData := .empty } evm.message.currentTarget) :=
    paid.keep rfl rfl rfl rfl
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact (skipCall_moves (gas := 0) pre.weaken hs).toFollows
  obtain ⟨address, -, h⟩ := Base.bind_ok_iff.mp h
  have c0 := (pre.trans (accessAddress_moves _ address)).trans
    (recordAccountRead_moves _ address)
  rcases keepReads_eq_ok_halt h with hr | ⟨e, -, he, rfl⟩
  · obtain ⟨e1, h1, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨e2, h2, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨state, -, hr⟩ := Base.bind_ok_iff.mp hr
    have c2 : Moves takes 0 price before { e2 with state } :=
      (((c0.trans (chargeStateGas_moves h1)).trans (chargeGas_moves h2)).weaken (t' := takes)
        (l' := 0) (p' := price)).keep rfl rfl rfl rfl
    split at hr
    · cases hr
      exact followsTablesChild_of_moves (c2.trans (drain_moves _)).weaken pos
        fun _ _ hres => resumeCreate_code_stack hres
    · obtain ⟨e3, h3, hr⟩ := Base.bind_ok_iff.mp hr
      cases hr
      exact (((c2.trans (refillStateGas_moves _ _)).trans (pushWord_moves h3)).trans
        (advance_moves _ _)).weaken.toFollows
  · exact FollowsTables.halt c0 (by omega) he

/-- A creation takes its words and pays at least its price, or halts once it has read the state. -/
theorem createStep_follows {create2 : Bool} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : createStep create2 evm = .ok result) :
    result.FollowsTables (if create2 then 4 else 3) 1 (createBaseCost fork) evm := by
  unfold createStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp [hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  rw [ite_eq_right_of_eq_false _ _ (eq_false hs)] at h
  obtain ⟨⟨value, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨start, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨size, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨salt, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨paid, h5, h⟩ := Base.bind_ok_iff.mp h
  have m := (((((popWord_moves h1).trans (popWord_moves h2)).trans (popWord_moves h3)).trans
    (popSalt_moves h4)).trans (chargeGasAndMemory_moves h5)).weaken
    (t' := if create2 then 4 else 3) (l' := 0) (p' := createBaseCost fork)
    (ht := by split <;> simp_all) (hl := by split <;> simp_all)
  unfold genericCreate at h
  split at h
  · cases h
  split at h
  · cases h
  exact launchCreate_follows m (by split <;> omega) h

/-- Each instruction that may send a message follows the tables. -/
theorem messageInstruction_follows {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} {evm : Evm fork Meter}
    {result : StepResult fork Meter} {takes leaves : Nat} {immediate : UInt8}
    (hrun : messageInstruction fork op = some run)
    (hw : op.stackWords immediate = some (takes, leaves)) (h : run evm = .ok result) :
    result.FollowsTables takes leaves (op.constantGas fork) evm := by
  unfold messageInstruction at hrun
  cases hc : callInstruction (Meter := Meter) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc <;>
      simp only [Op.stackWords, Option.some.injEq, Prod.mk.injEq] at hw <;>
      obtain ⟨rfl, rfl⟩ := hw
    all_goals first
      | (subst hc; exact callStep_follows h)
      | (split at hc
         · simp only [Option.some.injEq] at hc
           subst hc
           exact callStep_follows h
         · cases hc)
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun <;>
      simp only [Op.stackWords, Option.some.injEq, Prod.mk.injEq] at hw <;>
      obtain ⟨rfl, rfl⟩ := hw
    all_goals first
      | (subst hrun; exact createStep_follows h)
      | (split at hrun
         · simp only [Option.some.injEq] at hrun
           subst hrun
           exact createStep_follows h
         · cases hrun)

end EthLib.Execution.Evm
