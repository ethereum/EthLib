module

public import EthLib.Execution.Proofs.Evm.Logic.MeterSimulation
public import EthLib.Execution.Proofs.Evm.Call.Instructions
public import EthLib.Execution.Proofs.Evm.Logic.Message

/-!
# Proofs: the step of a call under the state gas meter

A call under the state gas meter of EIP-8037 passes on at least its gas under one counter.

Its caller keeps execution gas that covers the counter, and the two callers resume alike.

After GAS, the call under the state gas meter asks for more gas, by exactly its excess.

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

The call asks for `asked` with value `value`, and grows memory for `memoryCost`.

With more gas left, it may ask for up to that much more, as `asked'`. -/
theorem messageCallGas_mono {value : U256} {asked asked' low high memoryCost extraGas : Nat}
    (asks : asked ≤ asked') (gap : low + (asked' - asked) ≤ high)
    (paid : (messageCallGas fork value asked low memoryCost extraGas).cost + memoryCost ≤ low) :
    (messageCallGas fork value asked' high memoryCost extraGas).cost + memoryCost ≤ high ∧
      low - ((messageCallGas fork value asked low memoryCost extraGas).cost + memoryCost) ≤
        high - ((messageCallGas fork value asked' high memoryCost extraGas).cost + memoryCost) ∧
      (messageCallGas fork value asked low memoryCost extraGas).subCall ≤
        (messageCallGas fork value asked' high memoryCost extraGas).subCall := by
  simp only [messageCallGas, maxMessageCallGas] at paid ⊢
  by_cases tw : fork ≥ .tangerineWhistle <;>
    simp only [tw, true_and, false_and, ↓reduceIte] at paid ⊢
  · by_cases fits : extraGas + memoryCost ≤ low
    · simp only [fits, show extraGas + memoryCost ≤ high by omega, ↓reduceIte,
        Nat.min_def] at paid ⊢
      -- The cap of all but one 64th grows by at most the growth of the gas left.
      split <;> split <;> omega
    · simp only [fits, ↓reduceIte] at paid
      omega
  · omega

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

/-- A charge of execution gas keeps the relation, and an excess of execution gas over the counter.
-/
theorem chargeGas_ahead {excess : Nat} (t : Tracks start low high)
    (ahead : low.gas + excess ≤ high.gas.gasLeft) (amount : Nat) :
    Sim (fun l h => Tracks start l h ∧ l.gas + excess ≤ h.gas.gasLeft)
      (Evm.chargeGas low amount) (Evm.chargeGas high amount) := by
  refine ((t.chargeGas amount).and (fun _ ok => chargeGas_eq_ok_iff.mp ok)
    (fun _ ok => chargeGas_eq_ok_iff_charge.mp ok)).mono ?_
  rintro _ _ ⟨t, ⟨paid, rfl⟩, gas, charged, rfl⟩
  refine ⟨t, ?_⟩
  change StateGasMeter.charge high.gas amount = .ok gas at charged
  unfold StateGasMeter.charge at charged
  split at charged
  · cases charged
  · cases charged
    simp only
    omega

/-- A charge of state gas keeps the relation, and an excess of execution gas over the counter.

The state gas meter pays at most the same amount from its execution gas. -/
theorem chargeStateGas_ahead {excess : Nat} (t : Tracks start low high)
    (ahead : low.gas + excess ≤ high.gas.gasLeft) (amount : Nat) :
    Sim (fun l h => Tracks start l h ∧ l.gas + excess ≤ h.gas.gasLeft)
      (Evm.chargeStateGas low amount) (Evm.chargeStateGas high amount) := by
  refine ((t.chargeStateGas amount).and (fun _ ok => EthLib.Base.bind_ok_iff.mp ok)
    (fun _ ok => EthLib.Base.bind_ok_iff.mp ok)).mono ?_
  rintro _ _ ⟨t, ⟨gas, paid, hl⟩, ⟨meter, charged, hh⟩⟩
  simp only [pure, Except.pure, Except.ok.injEq] at hl hh
  subst hl hh
  refine ⟨t, ?_⟩
  change (if low.gas < amount then Except.error EvmError.outOfGas
    else Except.ok (low.gas - amount)) = Except.ok gas
    at paid
  change StateGasMeter.chargeState high.gas amount = .ok meter at charged
  unfold StateGasMeter.chargeState at charged
  split at paid
  · cases paid
  · cases paid
    split at charged
    · cases charged
      simp only
      omega
    · split at charged
      · cases charged
        simp only
        omega
      · cases charged

/-- The charge of a call, priced from the gas left of each frame, keeps the relation.

The call under the state gas meter may ask for more gas, by at most its excess of execution gas.

It then passes on at least as much gas. -/
theorem chargeCall (t : Tracks start low high) (value : U256) {asked asked' : Nat}
    (memoryCost extraGas : Nat) (asks : asked ≤ asked')
    (ahead : low.gas + (asked' - asked) ≤ high.gas.gasLeft) :
    Sim (fun l h => Tracks start l h ∧
        (messageCallGas fork value asked low.gas memoryCost extraGas).subCall ≤
          (messageCallGas fork value asked' high.gas.gasLeft memoryCost extraGas).subCall)
      (Evm.chargeGas low ((messageCallGas fork value asked low.gas memoryCost extraGas).cost +
        memoryCost))
      (Evm.chargeGas high
        ((messageCallGas fork value asked' high.gas.gasLeft memoryCost extraGas).cost +
          memoryCost)) := by
  obtain ⟨⟨meter, below, rfl⟩, hc, hf, hp, he⟩ := t
  have ahead : low.gas + (asked' - asked) ≤ meter.gasLeft := ahead
  refine ⟨fun after ok => ?_, ?_⟩
  · obtain ⟨paid, rfl⟩ := chargeGas_eq_ok_iff.mp ok
    obtain ⟨fits, keeps, more⟩ := messageCallGas_mono (fork := fork) (value := value)
      (memoryCost := memoryCost) (extraGas := extraGas) asks ahead paid
    refine ⟨withStateGas { low with gas := low.gas - _ }
      { meter with gasLeft := meter.gasLeft - _ }, ?_, ⟨⟨_, keeps, rfl⟩, hc, hf, hp, he⟩, more⟩
    simp only [Evm.chargeGas, gas_withStateGas, GasMeter.charge, StateGasMeter.charge,
      Nat.not_lt.mpr fits, ↓reduceIte, bind, Except.bind, pure, Except.pure]
    rfl
  · unfold Evm.chargeGas
    simp only [GasMeter.charge]
    split <;> simp [bind, Except.bind, pure, Except.pure]

/-- The payment of a call keeps the relation.

The call under the state gas meter may ask for more gas, by at most its excess of execution gas.

It then passes on at least as much gas. -/
theorem payCall (t : Tracks start low high) (kind : CallKind) (call : CallOperands)
    {asked : U256} (asks : call.gas.toNat ≤ asked.toNat)
    (ahead : low.gas + (asked.toNat - call.gas.toNat) ≤ high.gas.gasLeft)
    (memoryCost extraGas newAccount : Nat) :
    Sim (fun p q => p.1 ≤ q.1 ∧ Tracks start p.2 q.2)
      (Evm.payCall kind call memoryCost extraGas newAccount low)
      (Evm.payCall kind { call with gas := asked } memoryCost extraGas newAccount high) := by
  unfold Evm.payCall
  split
  · refine (t.chargeGas_ahead ahead _).bind fun _ _ ⟨t, ahead⟩ => ?_
    refine (t.chargeStateGas_ahead ahead _).bind fun _ _ ⟨t, ahead⟩ => ?_
    have h := t.chargeCall call.value 0 0 asks ahead
    simp only [Nat.add_zero] at h
    exact h.bind fun _ _ ⟨t, more⟩ => Sim.pure ⟨more, t⟩
  · exact (t.chargeCall call.value memoryCost extraGas asks ahead).bind
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

/-! ## The gas that a call asks for -/

/-- The frame under the state gas meter follows the frame under one counter, but for its top word.

That word is the gas that a call asks for.

Under the state gas meter, it may ask for more, by at most its excess of execution gas.

When the stack under one counter is empty, the other stack is free. -/
def AsksMore (low : Evm fork Nat) (high : Evm fork StateGasMeter) : Prop :=
  ∃ meter, { high with stack := low.stack } = withStateGas low meter ∧ low.gas ≤ meter.gasLeft ∧
    ∀ asked rest, low.stack.val = asked :: rest → ∃ asked', high.stack.val = asked' :: rest ∧
      asked.toNat ≤ asked'.toNat ∧ low.gas + (asked'.toNat - asked.toNat) ≤ meter.gasLeft

/-- A frame that follows asks for the same gas. -/
theorem FollowsMeter.asksMore {low : Evm fork Nat} {high : Evm fork StateGasMeter}
    (h : FollowsMeter low high) : AsksMore low high := by
  obtain ⟨meter, below, rfl⟩ := h
  exact ⟨meter, rfl, below, fun asked _ hs => ⟨asked, hs, Nat.le_refl _, by omega⟩⟩

/-- The pops of a call from a frame whose top word differs: only the gas asked differs. -/
theorem popCallOperands_top {Meter : Type} [GasMeter Meter] {kind : CallKind}
    {evm : Evm fork Meter} {stack : Stack} {asked asked' : U256} {rest : List U256}
    (hs : stack.val = asked :: rest) (hs' : evm.stack.val = asked' :: rest) :
    Evm.popCallOperands kind evm =
      (fun p => ({ p.1 with gas := asked' }, p.2)) <$>
        Evm.popCallOperands kind { evm with stack } := by
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  rcases stack with ⟨l', hl'⟩
  simp only at hs hs'
  subst hs hs'
  rcases rest with _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, l⟩⟩⟩⟩⟩⟩ <;>
    cases kind <;>
    simp [Evm.popCallOperands, popCallValue, CallKind.sendsValue, Evm.popWord, Stack.pop, bind,
      Except.bind, pure, Except.pure, Functor.map, Except.map]

/-- The pops of a call keep the relation, and the gas asked differs by at most the excess. -/
theorem AsksMore.popCallOperands {low : Evm fork Nat} {high : Evm fork StateGasMeter}
    (h : AsksMore low high) (kind : CallKind) :
    Sim (fun p q => ∃ asked, q.1 = { p.1 with gas := asked } ∧ p.1.gas.toNat ≤ asked.toNat ∧
        Tracks low p.2 q.2 ∧ p.2.gas + (asked.toNat - p.1.gas.toNat) ≤ q.2.gas.gasLeft)
      (Evm.popCallOperands kind low) (Evm.popCallOperands kind high) := by
  obtain ⟨meter, same, below, asks⟩ := h
  cases hs : low.stack.val with
  | nil =>
    have failed : Evm.popCallOperands kind low = .error .stackUnderflow :=
      popCallOperands_eq_error_iff.mpr ⟨by rw [hs]; split <;> decide, rfl⟩
    rw [failed]
    exact Sim.error
  | cons asked rest =>
    obtain ⟨asked', hs', more, ahead⟩ := asks asked rest hs
    -- The pops from the frame under the state gas meter are the pops of the same stack.
    rw [popCallOperands_top hs hs', same]
    have sim := (Tracks.init (start := low) below).popCallOperands kind
    -- The pops under one counter take `asked` first, from the same stack.
    have first : Evm.popCallOperands kind low =
        (fun p => ({ p.1 with gas := asked }, p.2)) <$>
          Evm.popCallOperands kind { low with stack := low.stack } :=
      popCallOperands_top hs hs
    refine ⟨fun p hp => ?_, sim.2⟩
    obtain ⟨q, hq, sameCall, t⟩ := sim.1 p hp
    have gasAsked : p.1.gas = asked := by
      rw [first] at hp
      obtain ⟨r, -, rfl⟩ := EthLib.Base.map_ok_iff.mp hp
      rfl
    refine ⟨({ p.1 with gas := asked' }, q.2), by rw [hq, sameCall]; rfl, asked', rfl, ?_, t, ?_⟩
    · rw [gasAsked]
      exact more
    · rw [gasAsked, congrArg Evm.gas (popCallOperands_eq_ok hp),
        congrArg Evm.gas (popCallOperands_eq_ok hq)]
      exact ahead

/-- The access to a delegate keeps the gas. -/
theorem gas_accessDelegation {Meter : Type} [GasMeter Meter] {evm after : Evm fork Meter}
    {address : Base.Address} {known : Nat} {callee : Callee}
    (h : Evm.accessDelegation evm address known = .ok (callee, after)) : after.gas = evm.gas := by
  obtain ⟨code, -, h⟩ := EthLib.Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := EthLib.Base.bind_ok_iff.mp h
    obtain ⟨_, -, h⟩ := EthLib.Base.bind_ok_iff.mp h
    cases h
    exact (accessAddress_of_stack _ _ _).2
  · cases h
    rfl

/-! ## The step of a call -/

/-- The step of a call under one counter lifts to a frame that asks for more gas, within its excess.

It holds for every kind of call, at every fork. -/
theorem callStep_asks (kind : CallKind) {low : Evm fork Nat} {high : Evm fork StateGasMeter}
    (h : AsksMore low high) :
    StepLifts low (low.pc + 1) (callStep kind low) (callStep kind high) := by
  unfold callStep
  refine (h.popCallOperands kind).bindStepLifts ?_
  rintro ⟨call, l⟩ ⟨_, h⟩ ⟨asked, rfl, asks, t, ahead⟩
  obtain ⟨⟨meter, below, rfl⟩, hc, hf, hp, he⟩ := t
  dsimp only
  simp only [message_withStateGas, memory_withStateGas]
  by_cases static : fork ≥ .glamsterdam ∧ kind = .call ∧ l.message.isStatic = true ∧
      call.value ≠ 0
  · simp only [static, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
    exact StepLifts.error
  simp only [static, ↓reduceIte]
  have t : Tracks low l (withStateGas l meter) := ⟨⟨meter, below, rfl⟩, hc, hf, hp, he⟩
  obtain ⟨cold, ta⟩ := t.accessAddress call.address
  rw [cold]
  refine (ta.checkGas _).bindStepLifts fun _ _ _ => ?_
  refine (ta.recordAccountRead call.address).keepReadsStep ?_
  refine (((ta.recordAccountRead call.address).accessDelegation call.address _).and
    (fun _ ok => gas_accessDelegation ok) (fun _ ok => gas_accessDelegation ok)).bindStepLifts ?_
  rintro ⟨callee, l2⟩ ⟨_, h2⟩ ⟨⟨rfl, t2⟩, gasLow, gasHigh⟩
  refine t2.keepReadsStep ?_
  obtain ⟨⟨meter2, below2, rfl⟩, hc2, hf2, hp2, he2⟩ := t2
  have t2 : Tracks low l2 (withStateGas l2 meter2) := ⟨⟨meter2, below2, rfl⟩, hc2, hf2, hp2, he2⟩
  -- The pops and the accesses keep the gas of each frame, so the excess stays.
  have ahead2 : l2.gas + (asked.toNat - call.gas.toNat) ≤ meter2.gasLeft := by
    have lowKept : l2.gas = l.gas := gasLow.trans (accessAddress_of_stack l l.stack _).2
    have highKept : meter2 = meter :=
      gasHigh.trans (accessAddress_of_stack (withStateGas l meter) l.stack _).2
    rw [lowKept, highKept]
    exact ahead
  simp only [state_withStateGas]
  refine (t2.payCall kind call asks ahead2 _ _ _).bindStepLifts ?_
  rintro ⟨sub, l3⟩ ⟨sub', h3⟩ ⟨more, t3⟩
  exact finishCall_lifts t3 more

/-- The step of a call under one counter lifts to a state gas meter that covers the counter.

It holds for every kind of call, at every fork, whatever gas the call asks for. -/
theorem callStep_bridge (kind : CallKind) {evm : Evm fork Nat} {meter : StateGasMeter}
    (below : evm.gas ≤ meter.gasLeft) :
    StepLifts evm (evm.pc + 1) (callStep kind evm) (callStep kind (withStateGas evm meter)) :=
  callStep_asks kind (FollowsMeter.asksMore ⟨meter, below, rfl⟩)

/-! ## GAS right before a call -/

/-- The frames right after GAS: each has pushed its execution gas left, which fits a word.

Otherwise the frame under the state gas meter follows the frame under one counter. -/
def GasPending (low : Evm fork Nat) (high : Evm fork StateGasMeter) : Prop :=
  ∃ meter rest, { high with stack := low.stack } = withStateGas low meter ∧
    low.gas ≤ meter.gasLeft ∧ meter.gasLeft < 2 ^ 256 ∧
    low.stack.val = .ofNat 256 low.gas :: rest ∧ high.stack.val = .ofNat 256 meter.gasLeft :: rest

/-- After GAS, a call under the state gas meter asks for more gas, by exactly its excess. -/
theorem GasPending.asksMore {low : Evm fork Nat} {high : Evm fork StateGasMeter}
    (h : GasPending low high) : AsksMore low high := by
  obtain ⟨meter, rest, same, below, fits, hs, hs'⟩ := h
  refine ⟨meter, same, below, fun asked rest' hl => ?_⟩
  rw [hs] at hl
  obtain ⟨rfl, rfl⟩ := List.cons.inj hl
  refine ⟨_, hs', ?_, ?_⟩ <;>
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits,
      Nat.mod_eq_of_lt (show low.gas < 2 ^ 256 by omega)] <;> omega

/-- GAS has the same instruction under each meter. -/
theorem instruction_gas {Meter : Type} [GasMeter Meter] :
    instruction (Meter := Meter) fork .gas =
      some (readFrame OPCODE_GAS fun evm => .ofNat 256 (GasMeter.gasLeft evm.gas)) := by
  simp [instruction, stackOnlyStep, controlFlowStep, HOrElse.hOrElse, OrElse.orElse,
    Option.orElse]

/-- GAS under one counter never fails with a revert, and a success moves on by one.

GAS then pushes the execution gas left of each frame, when that of the state gas meter fits a word.
-/
theorem gasStep {run : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (dispatch : instruction fork .gas = some run) (low : Evm fork Nat) :
    run low ≠ .error .revert ∧ ∀ after, run low = .ok after →
      MeterFields low after (low.pc + 1) ∧ after.pc = low.pc + 1 ∧
        after.running = low.running ∧
        ∀ meter : StateGasMeter, low.gas ≤ meter.gasLeft → meter.gasLeft < 2 ^ 256 → ∃ high,
          (readFrame OPCODE_GAS fun evm => .ofNat 256 (GasMeter.gasLeft evm.gas))
            (withStateGas low meter) = .ok high ∧ GasPending after high := by
  rw [instruction_gas] at dispatch
  cases dispatch
  refine ⟨fun failed => ?_, fun after ok => ?_⟩
  · by_cases enough : low.gas < OPCODE_GAS <;>
      by_cases full : low.stack.val.length = STACK_LIMIT <;>
      simp [readFrame, Evm.chargeGas, GasMeter.charge, Evm.pushWord, Stack.push, enough, full,
        bind, Except.bind, pure, Except.pure] at failed
  unfold readFrame at ok
  obtain ⟨_, paid, ok⟩ := EthLib.Base.bind_ok_iff.mp ok
  obtain ⟨enough, rfl⟩ := chargeGas_eq_ok_iff.mp paid
  obtain ⟨_, pushed, ok⟩ := EthLib.Base.bind_ok_iff.mp ok
  simp only [pure, Except.pure, Except.ok.injEq] at ok
  subst ok
  obtain ⟨stack, hpush, hx⟩ := EthLib.Base.bind_ok_iff.mp pushed
  simp only [pure, Except.pure, Except.ok.injEq] at hx
  subst hx
  unfold Stack.push at hpush
  split at hpush
  · cases hpush
  rename_i notFull
  cases hpush
  refine ⟨⟨rfl, rfl, fun _ => .inl rfl, id, fun _ => rfl⟩, rfl, rfl, fun meter below fits => ?_⟩
  simp only [readFrame, Evm.chargeGas, gas_withStateGas, GasMeter.charge, StateGasMeter.charge,
    show ¬meter.gasLeft < OPCODE_GAS by omega, ↓reduceIte, bind, Except.bind, Evm.pushWord,
    Stack.push, stack_withStateGas, notFull, ↓reduceDIte, pure, Except.pure, Except.ok.injEq,
    exists_eq_left']
  exact ⟨{ meter with gasLeft := meter.gasLeft - OPCODE_GAS }, low.stack.val, rfl,
    by simp only [advance]; omega, by simp only; omega, rfl, rfl⟩

/-- A frame that asks for more gas is the frame under one counter, with its own meter and stack. -/
theorem AsksMore.eq {low : Evm fork Nat} {high : Evm fork StateGasMeter} (h : AsksMore low high) :
    ∃ meter, high = { withStateGas low meter with stack := high.stack } := by
  obtain ⟨meter, same, -⟩ := h
  exact ⟨meter, by rw [← same]⟩

end EthLib.Execution.Evm.Logic
