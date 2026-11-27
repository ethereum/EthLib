module

public import EthLib.Execution.Proofs.Evm.Logic.Symbolic
public import EthLib.Execution.Proofs.Evm.Instructions.ControlFlow
public import EthLib.Execution.Proofs.Evm.Instructions.EnvironmentData
public import EthLib.Execution.Proofs.Evm.Instructions.MemoryData
public import EthLib.Execution.Proofs.Evm.Instructions.Return
public import EthLib.Execution.Proofs.Evm.Instructions.Storage
public import EthLib.Execution.Proofs.Evm.Instructions.LogData
public import EthLib.Execution.Proofs.Evm.Instructions.AccountData
public import EthLib.Execution.Proofs.Evm.Machine.JumpDest

/-!
# Proofs: a conservative counter for the state gas meter

A one-counter meter pays both execution gas and state gas from its counter.

The state gas meter of EIP-8037 can pay state gas from its reservoir.

So its execution gas stays at least the counter when it starts there and makes the same payments.

The parts of the instructions here keep that bound, and every other field of the frame.

A frame that reverts keeps its gas, so a revert carries to the state gas meter too.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256 Address)

variable {fork : Fork}

/-! ## Two meters -/

/-- A frame with the same fields and a state gas meter in place of its counter. -/
def withStateGas (evm : Evm fork Nat) (meter : StateGasMeter) : Evm fork StateGasMeter :=
  ⟨evm.pc, evm.stack, evm.memory, evm.code, evm.validJumpDestinations, meter, evm.running,
    evm.message, evm.output, evm.returnData, evm.state, evm.substate, evm.error⟩

section Fields

variable (evm : Evm fork Nat) (meter : StateGasMeter)

/-- The frame with a state gas meter keeps the program counter. -/
@[simp] theorem pc_withStateGas : (withStateGas evm meter).pc = evm.pc := rfl
/-- The frame with a state gas meter keeps the stack. -/
@[simp] theorem stack_withStateGas : (withStateGas evm meter).stack = evm.stack := rfl
/-- The frame with a state gas meter keeps the memory. -/
@[simp] theorem memory_withStateGas : (withStateGas evm meter).memory = evm.memory := rfl
/-- The frame with a state gas meter keeps the code. -/
@[simp] theorem code_withStateGas : (withStateGas evm meter).code = evm.code := rfl
/-- The frame with a state gas meter keeps the jump destinations. -/
@[simp] theorem validJumpDestinations_withStateGas :
    (withStateGas evm meter).validJumpDestinations = evm.validJumpDestinations := rfl
/-- The frame with a state gas meter has the meter it is given. -/
@[simp] theorem gas_withStateGas : (withStateGas evm meter).gas = meter := rfl
/-- The frame with a state gas meter keeps the running flag. -/
@[simp] theorem running_withStateGas : (withStateGas evm meter).running = evm.running := rfl
/-- The frame with a state gas meter keeps the message. -/
@[simp] theorem message_withStateGas : (withStateGas evm meter).message = evm.message := rfl
/-- The frame with a state gas meter keeps the output. -/
@[simp] theorem output_withStateGas : (withStateGas evm meter).output = evm.output := rfl
/-- The frame with a state gas meter keeps the return data. -/
@[simp] theorem returnData_withStateGas :
    (withStateGas evm meter).returnData = evm.returnData := rfl
/-- The frame with a state gas meter keeps the state. -/
@[simp] theorem state_withStateGas : (withStateGas evm meter).state = evm.state := rfl
/-- The frame with a state gas meter keeps the substate. -/
@[simp] theorem substate_withStateGas : (withStateGas evm meter).substate = evm.substate := rfl
/-- The frame with a state gas meter keeps the error. -/
@[simp] theorem error_withStateGas : (withStateGas evm meter).error = evm.error := rfl

end Fields

/-- The frames agree outside their meters, and the execution gas covers the counter. -/
def FollowsMeter (low : Evm fork Nat) (high : Evm fork StateGasMeter) : Prop :=
  ∃ meter, low.gas ≤ meter.gasLeft ∧ high = withStateGas low meter

/-- A payment of execution gas preserves the lower bound given by the counter. -/
theorem charge_followsMeter {gas after amount : Nat} {meter : StateGasMeter}
    (below : gas ≤ meter.gasLeft) (paid : GasMeter.charge gas amount = .ok after) :
    ∃ next, meter.charge amount = .ok next ∧ after ≤ next.gasLeft := by
  simp only [GasMeter.charge] at paid
  split at paid
  · cases paid
  · cases paid
    refine ⟨{ meter with gasLeft := meter.gasLeft - amount }, ?_, ?_⟩
    · simp only [StateGasMeter.charge, ite_eq_right (show ¬meter.gasLeft < amount by omega)]
    · simp only
      omega

/-- A payment of state gas preserves the lower bound given by the counter. -/
theorem chargeState_followsMeter {gas after amount : Nat} {meter : StateGasMeter}
    (below : gas ≤ meter.gasLeft) (paid : GasMeter.chargeState gas amount = .ok after) :
    ∃ next, meter.chargeState amount = .ok next ∧ after ≤ next.gasLeft := by
  simp only [GasMeter.chargeState] at paid
  split at paid
  · cases paid
  · cases paid
    by_cases reservoir : amount ≤ meter.reservoir
    · refine ⟨{ meter with reservoir := meter.reservoir - amount }, ?_, ?_⟩
      · simp only [StateGasMeter.chargeState, ite_eq_left reservoir]
      · simp only
        omega
    · refine ⟨{ meter with
          reservoir := 0
          gasLeft := meter.gasLeft - (amount - meter.reservoir)
          spill := meter.spill + (amount - meter.reservoir) }, ?_, ?_⟩
      · simp only [StateGasMeter.chargeState, ite_eq_right reservoir,
          ite_eq_left (show amount ≤ meter.reservoir + meter.gasLeft by omega)]
      · simp only
        omega

/-- A rollback of a revert cannot lower the execution gas that covers the counter. -/
theorem rollback_followsMeter {gas : Nat} {meter : StateGasMeter} (below : gas ≤ meter.gasLeft) :
    GasMeter.rollback gas ≤ (GasMeter.rollback meter).gasLeft := by
  change gas ≤ (StateGasMeter.restore meter).gasLeft
  simp only [StateGasMeter.restore]
  omega

/-- A refill cannot lower the execution gas that covers the counter. -/
theorem refill_followsMeter {gas amount : Nat} {meter : StateGasMeter}
    (below : gas ≤ meter.gasLeft) :
    GasMeter.refill gas amount ≤ (meter.refill amount).gasLeft := by
  simp only [GasMeter.refill, StateGasMeter.refill]
  omega

/-! ## Runs under the two meters -/

/-- Each success of the run under one counter has a success of the run under the state gas meter.

The two results are related by `R`.

The run under one counter never fails with the error of a revert. -/
def Sim {α β : Type} (R : α → β → Prop) (low : Except EvmError α) (high : Except EvmError β) :
    Prop :=
  (∀ a, low = .ok a → ∃ b, high = .ok b ∧ R a b) ∧ low ≠ .error .revert

namespace Sim

variable {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}

/-- Two successes whose values are related. -/
theorem ok {a : α} {b : β} (h : R a b) : Sim R (.ok a) (.ok b) :=
  ⟨fun _ ha => ⟨b, rfl, by cases ha; exact h⟩, nofun⟩

/-- Two returns whose values are related. -/
theorem pure {a : α} {b : β} (h : R a b) : Sim R (Pure.pure a) (Pure.pure b) := ok h

/-- A failure of the run under one counter, other than a revert, asks nothing of the other run.
-/
theorem error {e : EvmError} {high : Except EvmError β}
    (other : e ≠ .revert := by intro h; cases h) : Sim R (.error e) high :=
  ⟨fun _ ha => (by cases ha), fun h => other (Except.error.inj h)⟩

/-- A throw of the run under one counter, other than a revert, asks nothing of the other run. -/
theorem throw {e : EvmError} {high : Except EvmError β}
    (other : e ≠ .revert := by intro h; cases h) : Sim R (MonadExcept.throw e) high :=
  error other

/-- Two runs in sequence, with related first results and related rests. -/
theorem bind {low : Except EvmError α} {high : Except EvmError β}
    {f : α → Except EvmError γ} {g : β → Except EvmError δ} (h : Sim R low high)
    (rest : ∀ a b, R a b → Sim S (f a) (g b)) : Sim S (low >>= f) (high >>= g) := by
  refine ⟨fun c hc => ?_, fun hc => ?_⟩
  · obtain ⟨a, ha, hf⟩ := EthLib.Base.bind_ok_iff.mp hc
    obtain ⟨b, hb, hab⟩ := h.1 a ha
    obtain ⟨d, hd, hcd⟩ := (rest a b hab).1 c hf
    exact ⟨d, by rw [hb]; exact hd, hcd⟩
  · cases ha : low with
    | error e =>
      rw [ha] at hc h
      change Except.error e = _ at hc
      exact h.2 (by rw [Except.error.inj hc])
    | ok a =>
      rw [ha] at hc
      obtain ⟨b, -, hab⟩ := h.1 a ha
      exact (rest a b hab).2 hc

/-- A weaker relation of the results. -/
theorem mono {low : Except EvmError α} {high : Except EvmError β} {R' : α → β → Prop}
    (h : Sim R low high) (weaker : ∀ a b, R a b → R' a b) : Sim R' low high :=
  ⟨fun a ha =>
    let ⟨b, hb, hab⟩ := h.1 a ha
    ⟨b, hb, weaker a b hab⟩, h.2⟩

/-- A run that never fails with the error of a revert, related to itself by equality. -/
theorem refl {low : Except EvmError α} (other : low ≠ .error .revert) : Sim (· = ·) low low :=
  ⟨fun a ha => ⟨a, ha, rfl⟩, other⟩

/-- A read that fails only with an error of the state, related to itself by equality. -/
theorem ofState {x : Except State.StateError α} :
    Sim (· = ·) (x.mapError .state) (x.mapError .state) :=
  refl (by cases x <;> simp [Except.mapError])

/-- A branch on one condition in both runs. -/
theorem ite {c : Prop} [Decidable c] {x₁ x₂ : Except EvmError α} {y₁ y₂ : Except EvmError β}
    (yes : c → Sim R x₁ y₁) (no : ¬c → Sim R x₂ y₂) :
    Sim R (if c then x₁ else x₂) (if c then y₁ else y₂) := by
  by_cases h : c
  · simp only [h, ↓reduceIte]
    exact yes h
  · simp only [h, ↓reduceIte]
    exact no h

end Sim

/-! ## The fields that an instruction keeps -/

/-- The code and flags stay, and a running result advances or reaches a valid jump destination.

A normal result can only follow a frame with no error, and a running result keeps the error. -/
def MeterFields (before after : Evm fork Nat) (next : Nat) : Prop :=
  after.code = before.code ∧ after.validJumpDestinations = before.validJumpDestinations ∧
    (after.running = true → after.pc = next ∨
      isValidJumpDest before.validJumpDestinations after.pc = true) ∧
    (after.error = none → before.error = none) ∧ (after.running = true → after.error = before.error)

/-- An error that the state gas meter carries: none, or a revert, which keeps the gas left. -/
def Carried (error : Option EvmError) : Prop :=
  error = none ∨ error = some .revert

/-- The high frame follows the low frame.

The low frame keeps the code, the flags, the program counter and the error of `start`.

It holds inside an instruction, before the instruction moves the program counter. -/
def Tracks (start low : Evm fork Nat) (high : Evm fork StateGasMeter) : Prop :=
  FollowsMeter low high ∧ low.code = start.code ∧
    low.validJumpDestinations = start.validJumpDestinations ∧ low.pc = start.pc ∧
    low.error = start.error

/-- The high frame follows the low frame, which keeps the fields of `start` and moves on to `next`.
-/
def Lands (start : Evm fork Nat) (next : Nat) (low : Evm fork Nat)
    (high : Evm fork StateGasMeter) : Prop :=
  FollowsMeter low high ∧ MeterFields start low next

/-- Each success of the run under one counter keeps the fields of `start` and moves on to `next`.

Each success whose error is none or a revert has a success of the run under the state gas meter.

That success follows it, and the run under one counter never fails with the error of a revert. -/
def Lifts (start : Evm fork Nat) (next : Nat) (low : Except EvmError (Evm fork Nat))
    (high : Except EvmError (Evm fork StateGasMeter)) : Prop :=
  (∀ after, low = .ok after → MeterFields start after next ∧
    (Carried after.error → ∃ b, high = .ok b ∧ FollowsMeter after b)) ∧ low ≠ .error .revert

/-- Runs whose successes land lift. -/
theorem Sim.lifts {start : Evm fork Nat} {next : Nat} {low : Except EvmError (Evm fork Nat)}
    {high : Except EvmError (Evm fork StateGasMeter)} (h : Sim (Lands start next) low high) :
    Lifts start next low high :=
  ⟨fun after ok =>
    let ⟨b, hb, follows, fields⟩ := h.1 after ok
    ⟨fields, fun _ => ⟨b, hb, follows⟩⟩, h.2⟩

/-- A failure of the run under one counter, other than a revert, lifts. -/
theorem Lifts.error {start : Evm fork Nat} {next : Nat} {e : EvmError}
    {high : Except EvmError (Evm fork StateGasMeter)} (other : e ≠ .revert := by intro h; cases h) :
    Lifts start next (.error e) high :=
  ⟨fun _ h => (nomatch h), fun h => other (Except.error.inj h)⟩

/-- A run with related first results, then rests that lift. -/
theorem Sim.bindLifts {α β : Type} {R : α → β → Prop} {start : Evm fork Nat} {next : Nat}
    {low : Except EvmError α} {high : Except EvmError β}
    {f : α → Except EvmError (Evm fork Nat)} {g : β → Except EvmError (Evm fork StateGasMeter)}
    (h : Sim R low high) (rest : ∀ a b, R a b → Lifts start next (f a) (g b)) :
    Lifts start next (low >>= f) (high >>= g) := by
  refine ⟨fun c hc => ?_, fun hc => ?_⟩
  · obtain ⟨a, ha, hf⟩ := EthLib.Base.bind_ok_iff.mp hc
    obtain ⟨b, hb, hab⟩ := h.1 a ha
    refine ⟨((rest a b hab).1 c hf).1, fun carried => ?_⟩
    obtain ⟨d, hd, hcd⟩ := ((rest a b hab).1 c hf).2 carried
    exact ⟨d, by rw [hb]; exact hd, hcd⟩
  · cases ha : low with
    | error e =>
      rw [ha] at hc h
      change Except.error e = _ at hc
      exact h.2 (by rw [Except.error.inj hc])
    | ok a =>
      rw [ha] at hc
      obtain ⟨b, -, hab⟩ := h.1 a ha
      exact (rest a b hab).2 hc

/-- An instruction under one counter, and the same instruction under the state gas meter.

Each result of the first whose error is none or a revert has a matching result of the second. -/
def Bridge (width : Nat) (low : Evm fork Nat → Except EvmError (Evm fork Nat))
    (high : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)) : Prop :=
  -- Each success of the first keeps the code and the flags.
  --
  -- When it runs on, it moves the program counter by `width` or to a valid jump destination.
  --
  -- The second starts from execution gas that covers the counter.
  --
  -- An exceptional halt asks nothing of the second, and the first never fails with a revert.
  ∀ evm meter, evm.gas ≤ meter.gasLeft →
    Lifts evm (evm.pc + width) (low evm) (high (withStateGas evm meter))

/-- An instruction whose successes have related successes under the state gas meter is a bridge.
-/
theorem Bridge.of_sim {width : Nat} {low : Evm fork Nat → Except EvmError (Evm fork Nat)}
    {high : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    (h : ∀ evm meter, evm.gas ≤ meter.gasLeft →
      Sim (Lands evm (evm.pc + width)) (low evm) (high (withStateGas evm meter))) :
    Bridge width low high := fun evm meter below => (h evm meter below).lifts

namespace Tracks

variable {start low : Evm fork Nat} {high : Evm fork StateGasMeter}

/-- A frame and its frame with a state gas meter that covers its counter. -/
theorem init {meter : StateGasMeter} (below : start.gas ≤ meter.gasLeft) :
    Tracks start start (withStateGas start meter) :=
  ⟨⟨meter, below, rfl⟩, rfl, rfl, rfl, rfl⟩

/-- A move of the program counter by `width` lands on `start.pc + width`. -/
theorem advance (t : Tracks start low high) (width : Nat) :
    Lands start (start.pc + width) (Evm.advance low width) (Evm.advance high width) := by
  obtain ⟨⟨meter, below, rfl⟩, code, flags, pc, error⟩ := t
  exact ⟨⟨meter, below, rfl⟩, code, flags, fun _ => .inl (by simp [Evm.advance, pc]),
    fun h => error ▸ h, fun _ => error⟩

/-- A pop takes the same word, and keeps the relation. -/
theorem popWord (t : Tracks start low high) :
    Sim (fun p q => p.1 = q.1 ∧ Tracks start p.2 q.2) (Evm.popWord low) (Evm.popWord high) := by
  obtain ⟨⟨meter, below, rfl⟩, hc, hf, hp, he⟩ := t
  rcases low with ⟨pc, ⟨_ | ⟨x, rest⟩, hs⟩, memory, code, flags, gas, running, message, output,
    returnData, state, substate, error⟩
  · exact Sim.error
  · exact Sim.ok ⟨rfl, ⟨meter, below, rfl⟩, hc, hf, hp, he⟩

/-- A push of the same word keeps the relation. -/
theorem pushWord (t : Tracks start low high) (x : U256) :
    Sim (Tracks start) (Evm.pushWord low x) (Evm.pushWord high x) := by
  obtain ⟨⟨meter, below, rfl⟩, hc, hf, hp, he⟩ := t
  refine ⟨fun after ok => ?_, ?_⟩
  · obtain ⟨stack, hs, h⟩ := EthLib.Base.bind_ok_iff.mp ok
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨withStateGas { low with stack } meter, ?_, ⟨meter, below, rfl⟩, hc, hf, hp, he⟩
    change (low.stack.push x >>= fun stack => Pure.pure { withStateGas low meter with stack }) = _
    rw [hs]
    rfl
  · unfold Evm.pushWord Stack.push
    split <;> simp [bind, Except.bind, pure, Except.pure]

/-- A charge of execution gas keeps the relation. -/
theorem chargeGas (t : Tracks start low high) (amount : Nat) :
    Sim (Tracks start) (Evm.chargeGas low amount) (Evm.chargeGas high amount) := by
  obtain ⟨⟨meter, below, rfl⟩, hc, hf, hp, he⟩ := t
  refine ⟨fun after ok => ?_, ?_⟩
  · obtain ⟨gas, paid, h⟩ := EthLib.Base.bind_ok_iff.mp ok
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨next, hn, hb⟩ := charge_followsMeter below paid
    refine ⟨withStateGas { low with gas } next, ?_, ⟨next, hb, rfl⟩, hc, hf, hp, he⟩
    change (meter.charge amount >>= fun gas => Pure.pure { withStateGas low meter with gas }) = _
    rw [hn]
    rfl
  · unfold Evm.chargeGas
    simp only [GasMeter.charge]
    split <;> simp [bind, Except.bind, pure, Except.pure]

/-- A charge of state gas keeps the relation. -/
theorem chargeStateGas (t : Tracks start low high) (amount : Nat) :
    Sim (Tracks start) (Evm.chargeStateGas low amount) (Evm.chargeStateGas high amount) := by
  obtain ⟨⟨meter, below, rfl⟩, hc, hf, hp, he⟩ := t
  refine ⟨fun after ok => ?_, ?_⟩
  · obtain ⟨gas, paid, h⟩ := EthLib.Base.bind_ok_iff.mp ok
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨next, hn, hb⟩ := chargeState_followsMeter below paid
    refine ⟨withStateGas { low with gas } next, ?_, ⟨next, hb, rfl⟩, hc, hf, hp, he⟩
    change (meter.chargeState amount >>= fun gas => Pure.pure { withStateGas low meter with gas }) =
      _
    rw [hn]
    rfl
  · unfold Evm.chargeStateGas
    simp only [GasMeter.chargeState]
    split <;> simp [bind, Except.bind, pure, Except.pure]

/-- A charge of execution gas and of the growth of memory keeps the relation. -/
theorem chargeGasAndMemory (t : Tracks start low high) (cost : Nat)
    (ranges : List (U256 × U256)) :
    Sim (Tracks start) (Evm.chargeGasAndMemory low cost ranges)
      (Evm.chargeGasAndMemory high cost ranges) := by
  obtain ⟨⟨meter, below, rfl⟩, hc, hf, hp, he⟩ := t
  refine (chargeGas ⟨⟨meter, below, rfl⟩, hc, hf, hp, he⟩ _).bind fun l h t => ?_
  obtain ⟨⟨m, b, rfl⟩, hc, hf, hp, he⟩ := t
  exact Sim.pure ⟨⟨m, b, rfl⟩, hc, hf, hp, he⟩

/-- A pop of topics takes the same topics, and keeps the relation. -/
theorem popTopics (t : Tracks start low high) (n : Nat) :
    Sim (fun p q => p.1 = q.1 ∧ Tracks start p.2 q.2) (Evm.popTopics low n)
      (Evm.popTopics high n) := by
  induction n generalizing low high with
  | zero => exact Sim.ok ⟨rfl, t⟩
  | succ k ih =>
    refine t.popWord.bind ?_
    rintro ⟨x, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
    refine (ih t).bind ?_
    rintro ⟨ts, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
    exact Sim.pure ⟨rfl, t⟩

/-- A refill of state gas keeps the relation. -/
theorem refillStateGas (t : Tracks start low high) (amount : Nat) :
    Tracks start (Evm.refillStateGas low amount) (Evm.refillStateGas high amount) := by
  obtain ⟨⟨meter, below, rfl⟩, hc, hf, hp, he⟩ := t
  exact ⟨⟨meter.refill amount, refill_followsMeter below, rfl⟩, hc, hf, hp, he⟩

/-- A check of the gas left that passes under one counter passes under the state gas meter. -/
theorem checkGas (t : Tracks start low high) (amount : Nat) :
    Sim (fun _ _ => True) (Evm.checkGas low amount) (Evm.checkGas high amount) := by
  obtain ⟨⟨meter, below, rfl⟩, -⟩ := t
  refine ⟨fun _ ok => ?_, ?_⟩
  · refine ⟨(), ?_, trivial⟩
    unfold Evm.checkGas at ok ⊢
    split at ok
    · cases ok
    · rename_i pass
      split
      · rename_i fail
        exact absurd ⟨fail.1, Nat.lt_of_le_of_lt below fail.2⟩ pass
      · rfl
  · unfold Evm.checkGas
    split <;> simp [throw, throwThe, MonadExceptOf.throw, pure, Except.pure]

/-- The rest of an instruction that keeps its reads lifts when the rest lifts. -/
theorem keepReads {next : Nat} (t : Tracks start low high)
    {rest : Except EvmError (Evm fork Nat)} {highRest : Except EvmError (Evm fork StateGasMeter)}
    (h : Lifts start next rest highRest) :
    Lifts start next (Evm.keepReads low id rest) (Evm.keepReads high id highRest) := by
  obtain ⟨_, hc, hf, -, -⟩ := t
  refine ⟨fun after ok => ?_, fun hk => ?_⟩
  · cases hr : rest with
    | error e =>
      simp only [Evm.keepReads, hr] at ok
      split at ok
      · cases ok
      · cases ok
        refine ⟨⟨hc, hf, fun h => by simp [exceptionalHalt] at h,
          fun h => by simp [exceptionalHalt] at h, fun h => by simp [exceptionalHalt] at h⟩,
          fun carried => ?_⟩
        -- The rest fails with no revert, so the halt carries no error.
        rcases carried with hv | hv <;> simp only [id, exceptionalHalt, reduceCtorEq,
          Option.some.injEq] at hv
        subst hv
        exact (h.2 hr).elim
    | ok a =>
      simp only [Evm.keepReads, hr, Except.ok.injEq] at ok
      subst ok
      refine ⟨(h.1 a hr).1, fun carried => ?_⟩
      obtain ⟨b, hb, follows⟩ := (h.1 a hr).2 carried
      exact ⟨b, by simp only [Evm.keepReads, hb], follows⟩
  · cases hr : rest with
    | error e =>
      simp only [Evm.keepReads, hr] at hk
      split at hk
      · cases hk
        exact h.2 hr
      · cases hk
    | ok a => simp [Evm.keepReads, hr] at hk

end Tracks

end EthLib.Execution.Evm.Logic
