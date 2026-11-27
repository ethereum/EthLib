module

public import EthLib.Execution.Proofs.Evm.Logic.MeterSimulation

/-!
# Proofs: the step of a call under the state gas meter

A call under the state gas meter of EIP-8037 passes on at least its gas under one counter.

Its caller keeps execution gas that covers the counter, and the two callers resume alike.

Sources: the cap of [EIP-150][eip150] and the reservoir of [EIP-8037][eip8037].

[eip150]: https://eips.ethereum.org/EIPS/eip-150#specification
[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#transaction-level-gas-accounting-reservoir-model
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork}

/-! ## The relation of the results -/

/-- The message under the state gas meter is the one under one counter, with at least its gas.

It may also carry a reservoir. -/
def MessageCovers (low high : Message fork) : Prop :=
  low.gas ≤ high.gas ∧ high = { low with gas := high.gas, reservoir := high.reservoir }

/-- A result of a step under one counter relates to the run of that step under the state gas meter.

The step starts from `start`, and its next opcode is at `next`. -/
def ResultLifts (start : Evm fork Nat) (next : Nat) :
    StepResult fork Nat → Except EvmError (StepResult fork StateGasMeter) → Prop
  -- A frame keeps the fields of `start`.
  --
  -- When its error is none or a revert, the other run gives a frame that follows it.
  | .next after, high => MeterFields start after next ∧
      (Carried after.error → ∃ b, high = .ok (.next b) ∧ FollowsMeter after b)
  -- A message: the other run sends the message with at least its gas, and a reservoir.
  --
  -- Its caller follows the caller under one counter.
  | .child caller message resume, high => ∃ caller' message' resume',
      high = .ok (.child caller' message' resume') ∧ FollowsMeter caller caller' ∧
      MessageCovers message message' ∧
      -- Two frames that end the messages resume alike, when they follow each other.
      --
      -- Their messages may differ, but not in their current target.
      --
      -- A lift of whole runs gets this only for children that end with no error or a revert.
      --
      -- The child under the state gas meter can hold more gas, so it may succeed alone.
      ∀ child child', FollowsMeter child { child' with message := child.message } →
        child'.message.currentTarget = child.message.currentTarget →
        Lifts start next (resume child) (resume' child')

/-- Each result of a step under one counter has a related run under the state gas meter.

The step under one counter never fails with the error of a revert. -/
def StepLifts (start : Evm fork Nat) (next : Nat) (low : Except EvmError (StepResult fork Nat))
    (high : Except EvmError (StepResult fork StateGasMeter)) : Prop :=
  (∀ result, low = .ok result → ResultLifts start next result high) ∧ low ≠ .error .revert

/-! ## The gas of a call -/

/-- With more gas left, a call that the frame can pay passes on and keeps at least as much gas.

The call asks for `asked` with value `value`, and grows memory for `memoryCost`. -/
theorem messageCallGas_mono {value : U256} {asked low high memoryCost extraGas : Nat}
    (le : low ≤ high)
    (paid : (messageCallGas fork value asked low memoryCost extraGas).cost + memoryCost ≤ low) :
    (messageCallGas fork value asked high memoryCost extraGas).cost + memoryCost ≤ high ∧
      low - ((messageCallGas fork value asked low memoryCost extraGas).cost + memoryCost) ≤
        high - ((messageCallGas fork value asked high memoryCost extraGas).cost + memoryCost) ∧
      (messageCallGas fork value asked low memoryCost extraGas).subCall ≤
        (messageCallGas fork value asked high memoryCost extraGas).subCall := by
  simp only [messageCallGas, maxMessageCallGas] at paid ⊢
  by_cases tw : fork ≥ .tangerineWhistle <;>
    simp only [tw, true_and, false_and, ↓reduceIte] at paid ⊢
  · by_cases fits : extraGas + memoryCost ≤ low
    · simp only [fits, show extraGas + memoryCost ≤ high by omega, ↓reduceIte] at paid ⊢
      split <;> omega
    · simp only [fits, ↓reduceIte] at paid
      omega
  · split <;> omega

/-! ## Runs of the parts of a step -/

/-- A failure of the step under one counter, other than a revert, lifts. -/
theorem StepLifts.error {start : Evm fork Nat} {next : Nat} {e : EvmError}
    {high : Except EvmError (StepResult fork StateGasMeter)}
    (other : e ≠ .revert := by intro h; cases h) : StepLifts start next (.error e) high :=
  ⟨fun _ h => (nomatch h), fun h => other (Except.error.inj h)⟩

/-- A run with related first results, then rests of the step that lift. -/
theorem Sim.bindStepLifts {α β : Type} {R : α → β → Prop} {start : Evm fork Nat} {next : Nat}
    {low : Except EvmError α} {high : Except EvmError β}
    {f : α → Except EvmError (StepResult fork Nat)}
    {g : β → Except EvmError (StepResult fork StateGasMeter)}
    (h : Sim R low high) (rest : ∀ a b, R a b → StepLifts start next (f a) (g b)) :
    StepLifts start next (low >>= f) (high >>= g) := by
  refine ⟨fun c hc => ?_, fun hc => ?_⟩
  · obtain ⟨a, ha, hf⟩ := EthLib.Base.bind_ok_iff.mp hc
    obtain ⟨b, hb, hab⟩ := h.1 a ha
    have := (rest a b hab).1 c hf
    rw [hb]
    exact this
  · cases ha : low with
    | error e =>
      rw [ha] at hc h
      change Except.error e = _ at hc
      exact h.2 (by rw [Except.error.inj hc])
    | ok a =>
      rw [ha] at hc
      obtain ⟨b, -, hab⟩ := h.1 a ha
      exact (rest a b hab).2 hc

/-- A run of a frame that lifts gives a step that lifts. -/
theorem Lifts.next {start : Evm fork Nat} {next : Nat} {low : Except EvmError (Evm fork Nat)}
    {high : Except EvmError (Evm fork StateGasMeter)} (h : Lifts start next low high) :
    StepLifts start next (StepResult.next <$> low) (StepResult.next <$> high) := by
  refine ⟨fun r hr => ?_, fun hr => ?_⟩
  · cases hl : low with
    | error e => rw [hl] at hr; cases hr
    | ok a =>
      rw [hl] at hr
      cases hr
      refine ⟨(h.1 a hl).1, fun carried => ?_⟩
      obtain ⟨b, hb, follows⟩ := (h.1 a hl).2 carried
      exact ⟨b, by rw [hb]; rfl, follows⟩
  · cases hl : low with
    | error e => rw [hl] at hr; exact h.2 (by rw [hl]; cases hr; rfl)
    | ok a => rw [hl] at hr; cases hr

namespace Tracks

variable {start low : Evm fork Nat} {high : Evm fork StateGasMeter}

/-- The rest of a step that keeps its reads lifts when the rest lifts. -/
theorem keepReadsStep {next : Nat} (t : Tracks start low high)
    {rest : Except EvmError (StepResult fork Nat)}
    {highRest : Except EvmError (StepResult fork StateGasMeter)}
    (h : StepLifts start next rest highRest) :
    StepLifts start next (Evm.keepReads low .next rest) (Evm.keepReads high .next highRest) := by
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
        rcases carried with hv | hv <;> simp only [exceptionalHalt, reduceCtorEq,
          Option.some.injEq] at hv
        subst hv
        exact (h.2 hr).elim
    | ok a =>
      simp only [Evm.keepReads, hr, Except.ok.injEq] at ok
      subst ok
      have := h.1 a hr
      cases a with
      | next after =>
        refine ⟨this.1, fun carried => ?_⟩
        obtain ⟨b, hb, follows⟩ := this.2 carried
        exact ⟨b, by simp only [Evm.keepReads, hb], follows⟩
      | child caller message resume =>
        obtain ⟨c', m', r', hb, rest'⟩ := this
        exact ⟨c', m', r', by simp only [Evm.keepReads, hb], rest'⟩
  · cases hr : rest with
    | error e =>
      simp only [Evm.keepReads, hr] at hk
      split at hk
      · cases hk
        exact h.2 hr
      · cases hk
    | ok a => simp [Evm.keepReads, hr] at hk

/-- The pops of the operands of a call take the same operands, and keep the relation. -/
theorem popCallOperands (t : Tracks start low high) (kind : CallKind) :
    Sim (fun p q => p.1 = q.1 ∧ Tracks start p.2 q.2) (Evm.popCallOperands kind low)
      (Evm.popCallOperands kind high) := by
  unfold Evm.popCallOperands
  refine t.popWord.bind ?_
  rintro ⟨g, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨a, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine (show Sim (fun p q => p.1 = q.1 ∧ Tracks start p.2 q.2) (popCallValue kind _)
      (popCallValue kind _) by
    unfold popCallValue
    split
    · exact t.popWord
    · exact Sim.ok ⟨rfl, t⟩).bind ?_
  rintro ⟨v, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨i, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨isz, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨o, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨osz, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  exact Sim.pure ⟨rfl, t⟩

/-- An access to an address gives the same flag, and keeps the relation. -/
theorem accessAddress (t : Tracks start low high) (address : Base.Address) :
    (Evm.accessAddress high address).1 = (Evm.accessAddress low address).1 ∧
      Tracks start (Evm.accessAddress low address).2 (Evm.accessAddress high address).2 := by
  obtain ⟨⟨meter, below, rfl⟩, hc, hf, hp, he⟩ := t
  unfold Evm.accessAddress
  split
  · exact ⟨rfl, ⟨meter, below, rfl⟩, hc, hf, hp, he⟩
  · exact ⟨rfl, ⟨meter, below, rfl⟩, hc, hf, hp, he⟩

/-- A record of a read keeps the relation. -/
theorem recordAccountRead (t : Tracks start low high) (address : Base.Address) :
    Tracks start (Evm.recordAccountRead low address) (Evm.recordAccountRead high address) := by
  obtain ⟨⟨meter, below, rfl⟩, hc, hf, hp, he⟩ := t
  exact ⟨⟨meter, below, rfl⟩, hc, hf, hp, he⟩

/-- A read of the code of an account gives the same code. -/
theorem accountCode (t : Tracks start low high) (address : Base.Address) :
    Sim (· = ·) (Evm.accountCode low address) (Evm.accountCode high address) := by
  obtain ⟨⟨meter, below, rfl⟩, -⟩ := t
  exact Sim.ofState

/-- The access to a delegate gives the same code, and keeps the relation. -/
theorem accessDelegation (t : Tracks start low high) (address : Base.Address) (known : Nat) :
    Sim (fun p q => p.1 = q.1 ∧ Tracks start p.2 q.2) (Evm.accessDelegation low address known)
      (Evm.accessDelegation high address known) := by
  unfold Evm.accessDelegation
  refine (t.accountCode address).bind ?_
  rintro code _ rfl
  obtain ⟨⟨meter, below, rfl⟩, hc, hf, hp, he⟩ := t
  dsimp only
  split
  · rename_i delegate _
    have t' := (Tracks.accessAddress ⟨⟨meter, below, rfl⟩, hc, hf, hp, he⟩ delegate)
    obtain ⟨cold, t'⟩ := t'
    rw [cold]
    refine (t'.checkGas _).bind fun _ _ _ => ?_
    refine ((t'.recordAccountRead delegate).accountCode delegate).bind ?_
    rintro code' _ rfl
    exact Sim.pure ⟨rfl, t'.recordAccountRead delegate⟩
  · exact Sim.pure ⟨rfl, ⟨meter, below, rfl⟩, hc, hf, hp, he⟩

/-- The charge of a call, priced from the gas left of each frame, keeps the relation.

The call under the state gas meter passes on at least as much gas. -/
theorem chargeCall (t : Tracks start low high) (value : U256) (asked memoryCost extraGas : Nat) :
    Sim (fun l h => Tracks start l h ∧
        (messageCallGas fork value asked low.gas memoryCost extraGas).subCall ≤
          (messageCallGas fork value asked high.gas.gasLeft memoryCost extraGas).subCall)
      (Evm.chargeGas low ((messageCallGas fork value asked low.gas memoryCost extraGas).cost +
        memoryCost))
      (Evm.chargeGas high
        ((messageCallGas fork value asked high.gas.gasLeft memoryCost extraGas).cost +
          memoryCost)) := by
  obtain ⟨⟨meter, below, rfl⟩, hc, hf, hp, he⟩ := t
  refine ⟨fun after ok => ?_, ?_⟩
  · obtain ⟨paid, rfl⟩ := chargeGas_eq_ok_iff.mp ok
    obtain ⟨fits, keeps, more⟩ := messageCallGas_mono (fork := fork) (value := value)
      (asked := asked) (memoryCost := memoryCost) (extraGas := extraGas) below paid
    refine ⟨withStateGas { low with gas := low.gas - _ }
      { meter with gasLeft := meter.gasLeft - _ }, ?_, ⟨⟨_, keeps, rfl⟩, hc, hf, hp, he⟩, more⟩
    simp only [Evm.chargeGas, gas_withStateGas, GasMeter.charge, StateGasMeter.charge,
      Nat.not_lt.mpr fits, ↓reduceIte, bind, Except.bind, pure, Except.pure]
    rfl
  · unfold Evm.chargeGas
    simp only [GasMeter.charge]
    split <;> simp [bind, Except.bind, pure, Except.pure]

/-- The payment of a call keeps the relation.

The call under the state gas meter passes on at least as much gas. -/
theorem payCall (t : Tracks start low high) (kind : CallKind) (call : CallOperands)
    (memoryCost extraGas newAccount : Nat) :
    Sim (fun p q => p.1 ≤ q.1 ∧ Tracks start p.2 q.2)
      (Evm.payCall kind call memoryCost extraGas newAccount low)
      (Evm.payCall kind call memoryCost extraGas newAccount high) := by
  unfold Evm.payCall
  split
  · refine (t.chargeGas _).bind fun _ _ t => ?_
    refine (t.chargeStateGas _).bind fun _ _ t => ?_
    have h := t.chargeCall call.value call.gas.toNat 0 0
    simp only [Nat.add_zero] at h
    exact h.bind fun _ _ ⟨t, more⟩ => Sim.pure ⟨more, t⟩
  · exact (t.chargeCall call.value call.gas.toNat memoryCost extraGas).bind
      fun _ _ ⟨t, more⟩ => Sim.pure ⟨more, t⟩

end Tracks

/-- The execution gas of a caller and of its child adds up, at least, when the caller absorbs it. -/
theorem gasLeft_absorb (caller child : StateGasMeter) (succeeded : Bool) :
    caller.gasLeft + child.gasLeft ≤ (StateGasMeter.absorb caller child succeeded).gasLeft := by
  unfold StateGasMeter.absorb
  split
  · simp only [StateGasMeter.repay]
    omega
  · exact Nat.le_refl _

/-- A caller resumes alike from a frame with another message that has the same current target. -/
theorem resumeCall_message {Meter : Type} [GasMeter Meter] {caller child : Evm fork Meter}
    {newAccount : Nat} {outputStart outputSize : U256} {message : Message fork}
    (target : child.message.currentTarget = message.currentTarget) :
    resumeCall fork caller newAccount outputStart outputSize { child with message } =
      resumeCall fork caller newAccount outputStart outputSize child := by
  simp only [resumeCall, incorporateChild, touchedOnSuccess, touchedOnError, target]

/-- A caller that follows resumes alike from two frames that follow each other.

The two frames have the same current target. -/
theorem resumeCall_lifts {start caller : Evm fork Nat} {caller' : Evm fork StateGasMeter}
    (t : Tracks start caller caller') (newAccount : Nat) (outputStart outputSize : U256)
    {child : Evm fork Nat} {child' : Evm fork StateGasMeter}
    (ended : FollowsMeter child { child' with message := child.message })
    (target : child'.message.currentTarget = child.message.currentTarget) :
    Lifts start (start.pc + 1) (resumeCall fork caller newAccount outputStart outputSize child)
      (resumeCall fork caller' newAccount outputStart outputSize child') := by
  rw [← resumeCall_message target]
  obtain ⟨⟨meter, below, rfl⟩, hc, hf, hp, he⟩ := t
  obtain ⟨m, hm, ended⟩ := ended
  rw [ended]
  have merged : Tracks start (incorporateChild fork caller child)
      (withStateGas (incorporateChild fork caller child)
        (StateGasMeter.absorb meter m child.error.isNone)) := by
    refine ⟨⟨_, ?_, rfl⟩, ?_, ?_, ?_, ?_⟩ <;> unfold incorporateChild <;> split <;>
      simp only [hc, hf, hp, he]
    all_goals
      have := gasLeft_absorb meter m child.error.isNone
      simp only [GasMeter.absorb] at *
      omega
  have same : incorporateChild fork (withStateGas caller meter) (withStateGas child m) =
      withStateGas (incorporateChild fork caller child)
        (StateGasMeter.absorb meter m child.error.isNone) := by
    unfold incorporateChild
    simp only [error_withStateGas]
    by_cases e : child.error.isNone = true <;> simp only [e, ↓reduceIte, Bool.false_eq_true] <;> rfl
  unfold resumeCall
  simp only [same, error_withStateGas, output_withStateGas]
  have refilled : Tracks start
      (if child.error.isNone = true then incorporateChild fork caller child
        else refillStateGas (incorporateChild fork caller child) newAccount)
      (if child.error.isNone = true then
        withStateGas (incorporateChild fork caller child)
          (StateGasMeter.absorb meter m child.error.isNone)
        else refillStateGas (withStateGas (incorporateChild fork caller child)
          (StateGasMeter.absorb meter m child.error.isNone)) newAccount) := by
    split
    · exact merged
    · exact merged.refillStateGas newAccount
  generalize (if child.error.isNone = true then incorporateChild fork caller child
    else refillStateGas (incorporateChild fork caller child) newAccount) = l at refilled
  generalize (if child.error.isNone = true then _ else _) = h at refilled
  obtain ⟨⟨meter', below', rfl⟩, hc', hf', hp', he'⟩ := refilled
  refine (Sim.bind (Tracks.pushWord (low := { l with returnData := child.output })
    ⟨⟨meter', below', rfl⟩, hc', hf', hp', he'⟩ _) fun a b t => ?_).lifts
  obtain ⟨⟨meter'', below'', rfl⟩, hc'', hf'', hp'', he''⟩ := t
  exact Sim.pure (Tracks.advance (low := { a with
      memory := memoryWrite a.memory outputStart.toNat
        (child.output.extract 0 (min outputSize.toNat child.output.size)) })
    ⟨⟨meter'', below'', rfl⟩, hc'', hf'', hp'', he''⟩ 1)

/-- A call that runs no message gives back what each frame passes on, and keeps the relation. -/
theorem skipCall_lifts {start low : Evm fork Nat} {high : Evm fork StateGasMeter}
    (t : Tracks start low high) {gas gas' reservoir reservoir' : Nat} (more : gas ≤ gas') :
    Lifts start (start.pc + 1) (skipCall low gas reservoir) (skipCall high gas' reservoir') := by
  obtain ⟨⟨meter, below, rfl⟩, hc, hf, hp, he⟩ := t
  unfold skipCall
  have credited : Tracks start
      { low with
        gas := GasMeter.credit low.gas gas reservoir
        returnData := .empty }
      (withStateGas
        { low with
          gas := GasMeter.credit low.gas gas reservoir
          returnData := .empty }
        (GasMeter.credit meter gas' reservoir')) := by
    refine ⟨⟨_, ?_, rfl⟩, hc, hf, hp, he⟩
    simp only [GasMeter.credit, StateGasMeter.cancel, StateGasMeter.start]
    omega
  refine (Sim.bind (credited.pushWord 0) fun a b t => ?_).lifts
  exact Sim.pure (t.advance 1)

/-- The end of a call once it has paid keeps the relation, when it passes on more gas. -/
theorem finishCall_lifts {start low : Evm fork Nat} {high : Evm fork StateGasMeter}
    (t : Tracks start low high) {kind : CallKind} {call : CallOperands} {callee : Callee}
    {subCall subCall' newAccount expandBy : Nat} (more : subCall ≤ subCall') :
    StepLifts start (start.pc + 1) (finishCall kind call callee subCall newAccount expandBy low)
      (finishCall kind call callee subCall' newAccount expandBy high) := by
  obtain ⟨⟨meter, below, rfl⟩, hc, hf, hp, he⟩ := t
  unfold finishCall
  simp only [message_withStateGas]
  by_cases static : kind = .call ∧ low.message.isStatic = true ∧ call.value ≠ 0
  · simp only [static, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
    exact StepLifts.error
  simp only [static, ↓reduceIte]
  have caller : Tracks start (callerFrame low expandBy)
      (callerFrame (withStateGas low meter) expandBy) :=
    ⟨⟨StateGasMeter.drain meter, below, rfl⟩, hc, hf, hp, he⟩
  have same : callerFrame (withStateGas low meter) expandBy =
      withStateGas (callerFrame low expandBy) (StateGasMeter.drain meter) := rfl
  rw [same] at caller ⊢
  simp only [state_withStateGas, message_withStateGas]
  by_cases poor : ((callerFrame low expandBy).state.getAccount
      (callerFrame low expandBy).message.currentTarget).balance < call.value
  · simp only [poor, ↓reduceIte]
    exact (skipCall_lifts (caller.refillStateGas newAccount) more).next
  · simp only [poor, ↓reduceIte]
    unfold genericCall
    by_cases deep : (callerFrame low expandBy).message.depth + 1 > STACK_DEPTH_LIMIT
    · simp only [message_withStateGas, deep, ↓reduceIte]
      exact (skipCall_lifts (caller.refillStateGas newAccount) (by exact more)).next
    · simp only [message_withStateGas, deep, ↓reduceIte]
      refine ⟨fun r hr => ?_, nofun⟩
      cases hr
      refine ⟨_, _, _, rfl, ⟨meter.drain, below, rfl⟩, ⟨by exact more, rfl⟩,
        fun child child' ended target => ?_⟩
      exact resumeCall_lifts caller newAccount call.outputStart call.outputSize ended target

/-! ## The step of a call -/

/-- The step of a call under one counter lifts to a state gas meter that covers the counter.

It holds for every kind of call, at every fork, whatever gas the call asks for. -/
theorem callStep_bridge (kind : CallKind) {evm : Evm fork Nat} {meter : StateGasMeter}
    (below : evm.gas ≤ meter.gasLeft) :
    StepLifts evm (evm.pc + 1) (callStep kind evm) (callStep kind (withStateGas evm meter)) := by
  unfold callStep
  refine ((Tracks.init below).popCallOperands kind).bindStepLifts ?_
  rintro ⟨call, l⟩ ⟨_, h⟩ ⟨rfl, t⟩
  obtain ⟨⟨meter, below, rfl⟩, hc, hf, hp, he⟩ := t
  dsimp only
  simp only [message_withStateGas, memory_withStateGas]
  by_cases static : fork ≥ .glamsterdam ∧ kind = .call ∧ l.message.isStatic = true ∧
      call.value ≠ 0
  · simp only [static, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
    exact StepLifts.error
  simp only [static, ↓reduceIte]
  have t : Tracks evm l (withStateGas l meter) := ⟨⟨meter, below, rfl⟩, hc, hf, hp, he⟩
  obtain ⟨cold, ta⟩ := t.accessAddress call.address
  rw [cold]
  refine (ta.checkGas _).bindStepLifts fun _ _ _ => ?_
  refine (ta.recordAccountRead call.address).keepReadsStep ?_
  refine ((ta.recordAccountRead call.address).accessDelegation call.address _).bindStepLifts ?_
  rintro ⟨callee, l2⟩ ⟨_, h2⟩ ⟨rfl, t2⟩
  refine t2.keepReadsStep ?_
  obtain ⟨⟨meter2, below2, rfl⟩, hc2, hf2, hp2, he2⟩ := t2
  have t2 : Tracks evm l2 (withStateGas l2 meter2) := ⟨⟨meter2, below2, rfl⟩, hc2, hf2, hp2, he2⟩
  simp only [state_withStateGas]
  refine (t2.payCall kind call _ _ _).bindStepLifts ?_
  rintro ⟨sub, l3⟩ ⟨sub', h3⟩ ⟨more, t3⟩
  exact finishCall_lifts t3 more

end EthLib.Execution.Evm.Logic
