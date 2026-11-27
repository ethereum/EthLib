module

public import EthLib.Execution.Proofs.Evm.Logic.MeterReach
public import EthLib.Execution.Proofs.Evm.Logic.Message
public import Mathlib.Logic.Relation

/-!
# Proofs: runs that send messages under the state gas meter

A triple under an assumption on the frames that end messages carries to the state gas meter.

Under one counter, each message ends with the frame of the runner of the state gas meter.

That frame keeps at most the gas of the message under one counter.

Source: the reservoir of [EIP-8037][eip8037].

[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#transaction-level-gas-accounting-reservoir-model
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)

variable {fork : Fork}

/-! ## A frame under the state gas meter seen under one counter -/

/-- A frame under the state gas meter, seen under one counter as the frame that ends `message`.

Its execution gas is capped by the gas of `message`.

It carries `message`, with the current target of the frame, which its caller reads. -/
def lowerMeter (evm : Evm fork StateGasMeter) (message : Message fork) : Evm fork Nat :=
  ⟨evm.pc, evm.stack, evm.memory, evm.code, evm.validJumpDestinations,
    min evm.gas.gasLeft message.gas, evm.running,
    { message with currentTarget := evm.message.currentTarget }, evm.output, evm.returnData,
    evm.state, evm.substate, evm.error⟩

/-- A frame follows itself seen under one counter, with the message that it carries there. -/
theorem followsMeter_lowerMeter (evm : Evm fork StateGasMeter) (message : Message fork) :
    FollowsMeter (lowerMeter evm message)
      { evm with message := (lowerMeter evm message).message } :=
  ⟨evm.gas, Nat.min_le_left _ _, rfl⟩

/-- A frame seen under one counter holds at most the gas of its message. -/
theorem gasHeld_lowerMeter_le (evm : Evm fork StateGasMeter) (message : Message fork) :
    GasMeter.gasHeld (lowerMeter evm message).gas ≤ message.gas :=
  Nat.min_le_right _ _

/-! ## The gas of a call that sends a message -/

section Child

variable {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]

/-- A call that has paid more than the gas of its message sends it, and resumes its caller.

The caller and the message then hold less gas than the frame before the payment. -/
theorem finishCall_child_lt {kind : CallKind} {call : CallOperands} {callee : Callee}
    {subCall newAccount expandBy cost : Nat} {before evm caller : Evm fork Meter}
    {message : Message fork} {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (paid : Pays cost before evm) (lt : subCall < cost)
    (h : finishCall kind call callee subCall newAccount expandBy evm =
      .ok (.child caller message resume)) :
    GasMeter.gasHeld caller.gas + message.gas < GasMeter.gasHeld before.gas ∧
      ∃ newAccount outputStart outputSize,
        resume = resumeCall fork caller newAccount outputStart outputSize := by
  unfold finishCall at h
  split at h
  · cases h
  · dsimp only at h
    have paidCaller := (paid.callerFrame expandBy).gasHeld
    split at h
    · simp only [Functor.map, Except.map] at h
      split at h <;> cases h
    · unfold genericCall at h
      split at h
      · simp only [Functor.map, Except.map] at h
        split at h <;> cases h
      · cases h
        exact ⟨by simp only [callMessage]; omega, _, _, _, rfl⟩

/-- A call that sends a message resumes its caller.

The caller and the message hold less gas than the frame. -/
theorem callStep_child_lt {kind : CallKind} {evm caller : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : callStep kind evm = .ok (.child caller message resume)) :
    GasMeter.gasHeld caller.gas + message.gas < GasMeter.gasHeld evm.gas ∧
      ∃ newAccount outputStart outputSize,
        resume = resumeCall fork caller newAccount outputStart outputSize := by
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
  rcases keepReads_eq_ok h with h | ⟨e, he⟩
  · obtain ⟨⟨callee, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
    rcases keepReads_eq_ok h with h | ⟨e, he⟩
    · obtain ⟨⟨subCall, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨pos, above⟩ := callExtraGas_bounds (fork := fork) (kind := kind)
        (state := e3.state) (call := call) (cold := cold) (callee := callee)
      obtain ⟨cost, lt, p4⟩ := payCall_pays pos above h4
      have paid := ((((popCallOperands_pays h1).trans p2).trans
        (recordAccountRead_pays _ call.address)).trans (accessDelegation_pays h3)).trans p4
      exact finishCall_child_lt (paid.mono (by omega)) lt h
    · cases he
  · cases he

end Child

/-! ## Frames under one counter that stay ready -/

/-- Checked code with the flags of its scan, and no error while the frame runs. -/
def LowReady (low : Evm fork Nat) : Prop :=
  MeterReady low ∧ (low.running = true → low.error = none)

/-- A step of checked code keeps a frame ready. -/
theorem LowReady.step {low after : Evm fork Nat} (h : Step fork low after) (ready : LowReady low) :
    LowReady after := by
  obtain ⟨nextReady, -, keeps, -⟩ := step_meterReady h ready.1
  exact ⟨nextReady, fun runs => (keeps runs).trans (ready.2 h.running)⟩

/-- A call of checked code resumes as a lift asks, from any frame that ends its message.

The resume keeps the fields of the frame, moves on by one, and never fails with a revert. -/
theorem MeterReady.resumes {low caller : Evm fork Nat} {message : Message fork}
    {resume : Evm fork Nat → Except EvmError (Evm fork Nat)} (ready : MeterReady low)
    (running : low.running = true) (sent : step fork low = .ok (.child caller message resume))
    (child : Evm fork Nat) :
    (∀ after, resume child = .ok after → MeterFields low after (low.pc + 1)) ∧
      resume child ≠ .error .revert := by
  obtain ⟨kind, steps, -⟩ := ready.child running sent
  have called : callStep kind low = .ok (.child caller message resume) := by
    rw [← steps low rfl rfl]
    exact sent
  obtain ⟨_, _, _, -, -, -, resumes⟩ := (callStep_bridge kind (evm := low)
    (meter := StateGasMeter.start low.gas 0) (Nat.le_refl _)).1 _ called
  have lifted := resumes child (withStateGas child (StateGasMeter.start child.gas 0))
    ⟨_, Nat.le_refl _, rfl⟩ rfl
  exact ⟨fun after ok => (lifted.1 after ok).1, lifted.2⟩

/-- A call of checked code keeps a frame ready, once it resumes from any frame. -/
theorem LowReady.child {low caller child after : Evm fork Nat} {message : Message fork}
    {resume : Evm fork Nat → Except EvmError (Evm fork Nat)} (ready : LowReady low)
    (running : low.running = true) (sent : Evm.step fork low = .ok (.child caller message resume))
    (resumed : resume child = .ok after) : LowReady after := by
  obtain ⟨_, -, nextReady⟩ := ready.1.child running sent
  have fields := (ready.1.resumes running sent child).1 after resumed
  exact ⟨nextReady after fields, fun runs => (fields.2.2.2.2 runs).trans (ready.2 running)⟩

/-- A frame that halts exceptionally stays ready. -/
theorem LowReady.exceptionalHalt (low : Evm fork Nat) (ready : LowReady low) (e : EvmError) :
    LowReady (exceptionalHalt low e) :=
  ⟨⟨ready.1.1, ready.1.2.1, fun h => by cases h⟩, fun h => by cases h⟩

/-! ## The joint run -/

section Joint

variable {bound : Nat} (runChild : MessageRunner fork StateGasMeter bound)

/-- A step of a frame under one counter, with a step of a frame under the state gas meter.

When both send a message, the runner ends the message under the state gas meter.

The frame under one counter resumes from the frame that ends it, with the gas capped by its message.

The joint run stops when a resume fails.
-/
inductive JointStep :
    Evm fork Nat × Evm fork StateGasMeter → Evm fork Nat × Evm fork StateGasMeter → Prop where
  /-- Both frames step with no message. -/
  | step {low low' : Evm fork Nat} {high high' : Evm fork StateGasMeter} :
      Step fork low low' → Step fork high high' → JointStep (low, high) (low', high')
  /-- Both frames send a message, and resume from the frame that ends the second one. -/
  | child {low low' caller : Evm fork Nat} {high high' caller' : Evm fork StateGasMeter}
      {message message' : Message fork}
      {resume : Evm fork Nat → Except EvmError (Evm fork Nat)}
      {resume' : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
      {child : { child : Evm fork StateGasMeter // GasMeter.gasHeld child.gas ≤ message'.gas }} :
      low.running = true → high.running = true →
      Evm.step fork low = .ok (.child caller message resume) →
      Evm.step fork high = .ok (.child caller' message' resume') →
      ∀ lt : message'.gas < bound, runChild caller' message' lt = .ok child →
      resume (lowerMeter child.1 message) = .ok low' → resume' child.1 = .ok high' →
      JointStep (low, high) (low', high')

variable {runChild}

/-- The joint run gives one pair of frames from each pair. -/
theorem JointStep.deterministic {p q r : Evm fork Nat × Evm fork StateGasMeter}
    (hq : JointStep runChild p q) (hr : JointStep runChild p r) : q = r := by
  cases hq with
  | step hl hh =>
    cases hr with
    | step hl' hh' => rw [hl.deterministic hl', hh.deterministic hh']
    | child _ _ sent => exact (hl.not_child sent).elim
  | child _ _ sent sentH lt ran resumed resumedH =>
    cases hr with
    | step hl' _ => exact (hl'.not_child sent).elim
    | child _ _ sent' sentH' lt' ran' resumed' resumedH' =>
      rw [sent] at sent'
      cases sent'
      rw [sentH] at sentH'
      cases sentH'
      rw [ran] at ran'
      cases ran'
      rw [resumed] at resumed'
      cases resumed'
      rw [resumedH] at resumedH'
      cases resumedH'
      rfl

/-- A joint step under one counter holds at most the gas of the frame it starts from. -/
theorem JointStep.gasHeld_low {p q : Evm fork Nat × Evm fork StateGasMeter}
    (h : JointStep runChild p q) : GasMeter.gasHeld q.1.gas ≤ GasMeter.gasHeld p.1.gas := by
  cases h with
  | step hl _ => exact hl.gasHeld_le
  | child running _ sent _ _ _ resumed _ =>
    exact gasHeld_le_of_measure_lt
      ((step_decreases fork running sent).2 _ _ (gasHeld_lowerMeter_le _ _) resumed)

/-- A joint step under the state gas meter is a step under its runner. -/
theorem JointStep.stepBy {p q : Evm fork Nat × Evm fork StateGasMeter}
    (h : JointStep runChild p q) : StepBy fork bound runChild p.2 q.2 := by
  cases h with
  | step _ hh => exact .step hh
  | child _ running _ sentH lt ran _ resumedH => exact .child running sentH lt ran resumedH

/-- A frame reached in the joint run holds at most the gas of the first, under one counter. -/
theorem jointReaches_gasHeld_low {p q : Evm fork Nat × Evm fork StateGasMeter}
    (h : Relation.ReflTransGen (JointStep runChild) p q) :
    GasMeter.gasHeld q.1.gas ≤ GasMeter.gasHeld p.1.gas := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ hs ih => exact Nat.le_trans hs.gasHeld_low ih

variable (bound) in
/-- A ready pair: the frame under one counter is ready, and the other covers it when it may.

The frame under the state gas meter holds at most `bound`. -/
def JointReady (p : Evm fork Nat × Evm fork StateGasMeter) : Prop :=
  LowReady p.1 ∧ (Carried p.1.error → MeterCovers p.1 p.2) ∧ GasMeter.gasHeld p.2.gas ≤ bound

/-- From a ready pair whose first frame sends a message, the second sends a covering message.

The two callers resume alike, from frames that follow each other. -/
theorem JointReady.sends {low caller : Evm fork Nat} {high : Evm fork StateGasMeter}
    {message : Message fork} {resume : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (ready : JointReady bound (low, high)) (running : low.running = true)
    (sent : Evm.step fork low = .ok (.child caller message resume)) :
    ∃ caller' message' resume', Evm.step fork high = .ok (.child caller' message' resume') ∧
      high.running = true ∧ FollowsMeter caller caller' ∧ MessageCovers message message' ∧
      ∀ child child', FollowsMeter child { child' with message := child.message } →
        child'.message.currentTarget = child.message.currentTarget →
        Lifts low (low.pc + 1) (resume child) (resume' child') := by
  have covers : MeterCovers low high := ready.2.1 (.inl (ready.1.2 running))
  have lowReady : MeterReady low := ready.1.1
  obtain ⟨kind, steps, -⟩ := lowReady.child running sent
  obtain ⟨meter, same⟩ := covers.asksMore.eq
  have called : callStep kind low = .ok (.child caller message resume) := by
    rw [← steps low rfl rfl]
    exact sent
  obtain ⟨caller', message', resume', highOk, follows, covering, resumes⟩ :=
    (callStep_asks kind covers.asksMore).1 _ called
  refine ⟨caller', message', resume', ?_, ?_, follows, covering, resumes⟩
  · rw [steps high (by rw [same]; rfl) (by rw [same]; rfl)]
    exact highOk
  · rw [same]
    exact running

/-- A joint step keeps a pair ready. -/
theorem JointStep.ready {p q : Evm fork Nat × Evm fork StateGasMeter}
    (h : JointStep runChild p q) (ready : JointReady bound p) : JointReady bound q := by
  cases h with
  | step hl hh =>
    obtain ⟨-, -, -, lift⟩ := step_meterReady hl ready.1.1
    refine ⟨ready.1.step hl, fun carried => ?_, Nat.le_trans hh.gasHeld_le ready.2.2⟩
    obtain ⟨_, covers, hh'⟩ := lift carried _ (ready.2.1 (.inl (ready.1.2 hl.running)))
    rw [hh.deterministic hh']
    exact covers
  | @child low low' caller high high' caller' message message' resume resume' child running
      runningH sent sentH lt ran resumed resumedH =>
    obtain ⟨_, _, _, highOk, -, -, -, resumes⟩ := ready.sends running sent
    rw [sentH] at highOk
    cases highOk
    have lifted := resumes (lowerMeter child.1 message) child.1 (followsMeter_lowerMeter _ _)
      rfl
    have gasH := (StepBy.child runningH sentH lt ran resumedH).gasHeld_le
    refine ⟨ready.1.child running sent resumed, fun carried => ?_, Nat.le_trans gasH ready.2.2⟩
    obtain ⟨b, hb, follows⟩ := (lifted.1 _ resumed).2 carried
    rw [resumedH] at hb
    cases hb
    exact ⟨Nat.lt_of_le_of_lt gasH (ready.2.1 (.inl (ready.1.2 running))).1, .inl follows⟩

/-- Each pair of the joint run from a ready pair is ready. -/
theorem JointReady.reaches {p q : Evm fork Nat × Evm fork StateGasMeter}
    (h : Relation.ReflTransGen (JointStep runChild) p q) (ready : JointReady bound p) :
    JointReady bound q := by
  induction h with
  | refl => exact ready
  | tail _ hs ih => exact hs.ready ih

/-- A later pair of the joint run that sends the same message from the same caller is the earlier.

The frame under one counter that resumes holds at most the caller and its message. -/
theorem jointEvent_before {p q : Evm fork Nat × Evm fork StateGasMeter}
    {caller : Evm fork Nat} {message : Message fork}
    {resume resume₂ : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (h : Relation.ReflTransGen (JointStep runChild) p q) (pReady : JointReady bound p)
    (qReady : JointReady bound q) (pRuns : p.1.running = true) (qRuns : q.1.running = true)
    (sp : Evm.step fork p.1 = .ok (.child caller message resume))
    (sq : Evm.step fork q.1 = .ok (.child caller message resume₂)) : p = q := by
  rcases Relation.ReflTransGen.cases_head h with same | ⟨p1, first, rest⟩
  · exact same
  · exfalso
    rcases p with ⟨low, high⟩
    cases first with
    | step hl _ => exact hl.not_child sp
    | @child _ _ _ _ _ _ _ _ _ _ child _ _ sent _ _ _ resumed _ =>
      rw [sp] at sent
      cases sent
      obtain ⟨kind, steps, -⟩ := pReady.1.1.child pRuns sp
      have called : callStep kind low = .ok (.child caller message resume) := by
        rw [← steps low rfl rfl]
        exact sp
      obtain ⟨-, _, _, _, rfl⟩ := callStep_child_lt called
      have resumedGas := (resumeCall_gasHeld resumed).1
      have capped := gasHeld_lowerMeter_le child.1 message
      have along := jointReaches_gasHeld_low rest
      obtain ⟨kind₂, steps₂, -⟩ := qReady.1.1.child qRuns sq
      have called₂ : callStep kind₂ q.1 = .ok (.child caller message resume₂) := by
        rw [← steps₂ q.1 rfl rfl]
        exact sq
      have lt := (callStep_child_lt called₂).1
      simp only at along
      omega

/-- Two pairs of the joint run that send the same message from the same caller are one pair. -/
theorem jointEvent_unique {start p q : Evm fork Nat × Evm fork StateGasMeter}
    {caller : Evm fork Nat} {message : Message fork}
    {resume resume₂ : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (startReady : JointReady bound start)
    (hp : Relation.ReflTransGen (JointStep runChild) start p)
    (hq : Relation.ReflTransGen (JointStep runChild) start q)
    (pRuns : p.1.running = true) (qRuns : q.1.running = true)
    (sp : Evm.step fork p.1 = .ok (.child caller message resume))
    (sq : Evm.step fork q.1 = .ok (.child caller message resume₂)) : p = q := by
  have unique : Relator.RightUnique (JointStep runChild) := fun _ _ _ hb hc => hb.deterministic hc
  rcases Relation.ReflTransGen.total_of_right_unique unique hp hq with pq | qp
  · exact jointEvent_before pq (JointReady.reaches hp startReady)
      (JointReady.reaches hq startReady) pRuns qRuns sp sq
  · exact (jointEvent_before qp (JointReady.reaches hq startReady)
      (JointReady.reaches hp startReady) qRuns pRuns sq sp).symm

/-! ## The runner under one counter -/

open Classical in
variable (runChild) in
/-- The runner under one counter that answers each message of the joint run from `start`.

It ends the message as the runner of the state gas meter ends the message of the same pair.

The frame it gives holds at most the gas of the message under one counter.

It fails on any other message, with an error that aborts the run.

Any error that aborts would do, and no run of the proofs reaches it. -/
noncomputable def tableRunner (start : Evm fork Nat × Evm fork StateGasMeter) (boundLow : Nat) :
    MessageRunner fork Nat boundLow :=
  fun caller message _ =>
    if h : ∃ p, Relation.ReflTransGen (JointStep runChild) start p ∧ p.1.running = true ∧
        ∃ resume, Evm.step fork p.1 = .ok (.child caller message resume) then
      match Evm.step fork (Classical.choose h).2 with
      | .ok (.child caller' message' _) =>
        if lt : message'.gas < bound then
          (fun child => ⟨lowerMeter child.1 message, gasHeld_lowerMeter_le _ _⟩) <$>
            runChild caller' message' lt
        else .error (.forkNotYetSpecified fork)
      | _ => .error (.forkNotYetSpecified fork)
    else .error (.forkNotYetSpecified fork)

/-- On a message of a pair of the joint run, the runner under one counter ends the other message.

It gives the frame that ends it, with the gas capped by the message under one counter. -/
theorem tableRunner_eq {start : Evm fork Nat × Evm fork StateGasMeter} {boundLow : Nat}
    {low caller : Evm fork Nat} {high caller' : Evm fork StateGasMeter}
    {message message' : Message fork} {resume : Evm fork Nat → Except EvmError (Evm fork Nat)}
    {resume' : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    (startReady : JointReady bound start)
    (reached : Relation.ReflTransGen (JointStep runChild) start (low, high))
    (running : low.running = true) (sent : Evm.step fork low = .ok (.child caller message resume))
    (sentH : Evm.step fork high = .ok (.child caller' message' resume'))
    (lt : message'.gas < bound) (ltLow : message.gas < boundLow) :
    tableRunner runChild start boundLow caller message ltLow =
      (fun child => ⟨lowerMeter child.1 message, gasHeld_lowerMeter_le _ _⟩) <$>
        runChild caller' message' lt := by
  have h : ∃ p, Relation.ReflTransGen (JointStep runChild) start p ∧ p.1.running = true ∧
      ∃ resume, Evm.step fork p.1 = .ok (.child caller message resume) :=
    ⟨(low, high), reached, running, resume, sent⟩
  obtain ⟨chosenReached, chosenRuns, _, chosenSent⟩ := Classical.choose_spec h
  have same : Classical.choose h = (low, high) :=
    jointEvent_unique startReady chosenReached reached chosenRuns running chosenSent sent
  unfold tableRunner
  rw [dite_eq_left_of_eq_true (eq_true h), same]
  simp only [sentH, dite_eq_left_of_eq_true (eq_true lt)]

/-- A pair of the joint run that sends a message, as the runner under one counter sees it.

Its frame that ends the message comes from the runner of the state gas meter, with the gas capped.
-/
theorem tableRunner_ok {start : Evm fork Nat × Evm fork StateGasMeter} {boundLow : Nat}
    {caller : Evm fork Nat} {message : Message fork} {ltLow : message.gas < boundLow}
    {child : { child : Evm fork Nat // GasMeter.gasHeld child.gas ≤ message.gas }}
    (ran : tableRunner runChild start boundLow caller message ltLow = .ok child) :
    ∃ low high caller' message' resume resume' lt ended,
      Relation.ReflTransGen (JointStep runChild) start (low, high) ∧ low.running = true ∧
      Evm.step fork low = .ok (.child caller message resume) ∧
      Evm.step fork high = .ok (.child caller' message' resume') ∧
      runChild caller' message' lt = .ok ended ∧ child.1 = lowerMeter ended.1 message := by
  unfold tableRunner at ran
  split at ran
  · rename_i h
    obtain ⟨reached, runs, resume, sent⟩ := Classical.choose_spec h
    split at ran
    · rename_i caller' message' resume' sentH
      split at ran
      · rename_i lt
        obtain ⟨ended, ranH, rfl⟩ := EthLib.Base.map_ok_iff.mp ran
        exact ⟨_, _, caller', message', resume, resume', lt, ended, reached, runs, sent, sentH,
          ranH, rfl⟩
      · cases ran
    · cases ran
  · cases ran

/-- The runner under one counter fails only with an error of the other runner, or one that aborts.
-/
theorem tableRunner_error {start : Evm fork Nat × Evm fork StateGasMeter} {boundLow : Nat}
    {caller : Evm fork Nat} {message : Message fork} {ltLow : message.gas < boundLow}
    {e : EvmError} (ran : tableRunner runChild start boundLow caller message ltLow = .error e) :
    e.aborts = true ∨ ∃ caller' message' lt, runChild caller' message' lt = .error e := by
  unfold tableRunner at ran
  split at ran
  · split at ran
    · rename_i caller' message' _ _
      split at ran
      · rename_i lt
        cases hr : runChild caller' message' lt with
        | ok _ => simp [hr, Functor.map, Except.map] at ran
        | error e' =>
          simp only [hr, Functor.map, Except.map, Except.error.injEq] at ran
          subst ran
          exact .inr ⟨caller', message', lt, hr⟩
      · cases ran
        exact .inl rfl
    · cases ran
      exact .inl rfl
  · cases ran
    exact .inl rfl

/-- The runner under one counter meets the assumption under one counter.

The runner of the state gas meter meets its own assumption, which gives that one for capped frames.
-/
theorem tableRunner_meets {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {calleeH : Evm fork StateGasMeter → Message fork → Evm fork StateGasMeter → Prop}
    {start : Evm fork Nat × Evm fork StateGasMeter} {boundLow : Nat}
    (startReady : JointReady bound start) (meets : Meets calleeH runChild)
    (compat : ∀ caller caller' message message' child, FollowsMeter caller caller' →
      MessageCovers message message' → message'.gas < 2 ^ 256 → calleeH caller' message' child →
      callee caller message (lowerMeter child message)) :
    Meets callee (tableRunner runChild start boundLow) := by
  refine ⟨fun caller message ltLow child ran => ?_, fun caller message ltLow e ran => ?_⟩
  · obtain ⟨low, high, caller', message', resume, resume', lt, ended, reached, runs, sent, sentH,
      ranH, same⟩ := tableRunner_ok ran
    have ready := JointReady.reaches reached startReady
    obtain ⟨_, _, _, highOk, runsH, follows, covers, -⟩ := ready.sends runs sent
    rw [sentH] at highOk
    cases highOk
    rw [same]
    -- The message holds less gas than its caller, whose gas fits a word.
    have fits : message'.gas < 2 ^ 256 := Nat.lt_trans (step_decreases fork runsH sentH).1
      (ready.2.1 (.inl (ready.1.2 runs))).1
    exact compat _ _ _ _ _ follows covers fits (meets.ok _ _ _ _ ranH)
  · rcases tableRunner_error ran with aborts | ⟨_, _, _, ranH⟩
    · exact aborts
    · exact meets.aborts _ _ _ _ ranH

/-! ## Runs carried to the state gas meter -/

/-- A reach under the runner of one counter, from a pair of the joint run, carries.

It ends in `Q`, or on a message that its runner fails, under each meter. -/
theorem tableRunner_lift {Q : Evm fork Nat → Prop} {start : Evm fork Nat × Evm fork StateGasMeter}
    {boundLow : Nat} (startReady : JointReady bound start)
    (ends : ∀ low, Q low → Carried low.error) {low last : Evm fork Nat}
    (r : Reaches (StepBy fork boundLow (tableRunner runChild start boundLow)) low last)
    (endsIn : Q last ∨ AbortsBy fork boundLow (tableRunner runChild start boundLow) last) :
    ∀ {high}, Relation.ReflTransGen (JointStep runChild) start (low, high) →
      ∃ high', Reaches (StepBy fork bound runChild) high high' ∧
        ((∃ low', Q low' ∧ MeterCovers low' high') ∨ AbortsBy fork bound runChild high') := by
  induction r with
  | refl =>
    intro high reached
    have ready := JointReady.reaches reached startReady
    rcases endsIn with q | ⟨running, caller, message, resume, sent, ltLow, e, failed⟩
    · exact ⟨high, .refl _, .inl ⟨_, q, ready.2.1 (ends _ q)⟩⟩
    · obtain ⟨caller', message', resume', highOk, runsH, -, -, -⟩ := ready.sends running sent
      have lt : message'.gas < bound :=
        Nat.lt_of_lt_of_le (step_decreases fork runsH highOk).1 ready.2.2
      rw [tableRunner_eq startReady reached running sent highOk lt ltLow] at failed
      cases hr : runChild caller' message' lt with
      | ok _ => simp [hr, Functor.map, Except.map] at failed
      | error e' =>
        exact ⟨high, .refl _, .inr ⟨runsH, caller', message', resume', highOk, lt, e', hr⟩⟩
  | @step low next _ hs rest ih =>
    intro high reached
    have ready := JointReady.reaches reached startReady
    have lowReady : LowReady low := ready.1
    have nextReady : LowReady next := by
      cases hs with
      | step hl => exact lowReady.step hl
      | child running sent _ _ resumed => exact lowReady.child running sent resumed
      | childHalt => exact LowReady.exceptionalHalt _ lowReady _
    -- A frame that steps on runs, so it has no error; otherwise it ends the reach.
    have carried : Carried next.error := by
      cases rest with
      | refl =>
        rcases endsIn with q | aborted
        · exact ends _ q
        · exact .inl (nextReady.2 aborted.1)
      | step further _ => exact .inl (nextReady.2 further.running)
    cases hs with
    | step hl =>
      obtain ⟨-, -, -, lift⟩ := step_meterReady hl lowReady.1
      obtain ⟨high', -, hh⟩ := lift carried high (ready.2.1 (.inl (lowReady.2 hl.running)))
      obtain ⟨last', reach, fin⟩ := ih endsIn (reached.tail (.step hl hh))
      exact ⟨last', .step (.step hh) reach, fin⟩
    | @child _ _ message _ _ running sent ltLow ran resumed =>
      obtain ⟨caller', message', resume', highOk, runsH, -, -, resumes⟩ :=
        ready.sends running sent
      have lt : message'.gas < bound :=
        Nat.lt_of_lt_of_le (step_decreases fork runsH highOk).1 ready.2.2
      rw [tableRunner_eq startReady reached running sent highOk lt ltLow] at ran
      obtain ⟨ended, ranH, rfl⟩ := EthLib.Base.map_ok_iff.mp ran
      have lifted := resumes (lowerMeter ended.1 message) ended.1 (followsMeter_lowerMeter _ _)
        rfl
      obtain ⟨high', resumedH, -⟩ := (lifted.1 _ resumed).2 carried
      obtain ⟨last', reach, fin⟩ :=
        ih endsIn (reached.tail (.child running runsH sent highOk lt ranH resumed resumedH))
      exact ⟨last', .step (.child runsH highOk lt ranH resumedH) reach, fin⟩
    | @childHalt _ _ _ child e running sent _ _ failed _ =>
      -- The resume never fails with a revert, so the halt carries no error.
      exfalso
      rcases carried with h | h <;> simp only [exceptionalHalt, reduceCtorEq,
        Option.some.injEq] at h
      subst h
      exact (lowReady.1.resumes running sent child.1).2 failed

end Joint

/-! ## Triples carried to the state gas meter -/

/-- A triple under an assumption, over checked code, holds under the state gas meter.

The assumption under the state gas meter must give the one under one counter.

It must do so for a frame that ends a covering message, seen under one counter with its gas capped.

The frames of the postcondition must have no error, or a revert. -/
theorem HoareUnder.meterCovers {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {calleeH : Evm fork StateGasMeter → Message fork → Evm fork StateGasMeter → Prop}
    {P Q : Evm fork Nat → Prop} (h : HoareUnder fork callee P Q)
    -- Each frame of the precondition has checked code, its flags, an opcode position and no error.
    (ready : ∀ low, P low → SupportedCode low.code = true ∧
      low.validJumpDestinations = validJumpDestinations low.code ∧
      (low.code.size ≤ low.pc ∨ low.pc ∈ opcodePositions low.code) ∧ low.error = none)
    (ends : ∀ low, Q low → Carried low.error)
    -- A frame that ends a covering message meets the assumption under one counter, gas capped.
    (compat : ∀ caller caller' message message' child, FollowsMeter caller caller' →
      MessageCovers message message' → message'.gas < 2 ^ 256 → calleeH caller' message' child →
      callee caller message (lowerMeter child message)) :
    HoareUnder (Meter := StateGasMeter) fork calleeH (Covered P)
      fun high => ∃ low, Q low ∧ MeterCovers low high := by
  rintro bound runChild meets high ⟨low, hp, follows, fits⟩ within
  obtain ⟨supported, flags, boundary, normal⟩ := ready low hp
  have startReady : JointReady bound (low, high) :=
    ⟨⟨⟨supported, flags, fun _ => boundary⟩, fun _ => normal⟩, fun _ => ⟨fits, .inl follows⟩,
      within⟩
  obtain ⟨last, reach, endsIn⟩ := h low.gas (tableRunner runChild (low, high) low.gas)
    (tableRunner_meets startReady meets compat) low hp (Nat.le_refl _)
  exact tableRunner_lift startReady ends reach endsIn .refl

/-- A specification under an assumption, over checked code, holds under the state gas meter.

The frames of the postcondition must stop with no error, or with a revert. -/
theorem SpecUnder.covered {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {calleeH : Evm fork StateGasMeter → Message fork → Evm fork StateGasMeter → Prop}
    {P Q : Evm fork Nat → Prop} (h : SpecUnder fork callee P Q)
    (ready : ∀ low, P low → SupportedCode low.code = true ∧
      low.validJumpDestinations = validJumpDestinations low.code ∧
      (low.code.size ≤ low.pc ∨ low.pc ∈ opcodePositions low.code) ∧ low.error = none)
    (ends : ∀ low, Q low → Carried low.error)
    (compat : ∀ caller caller' message message' child, FollowsMeter caller caller' →
      MessageCovers message message' → message'.gas < 2 ^ 256 → calleeH caller' message' child →
      callee caller message (lowerMeter child message)) :
    SpecUnder (Meter := StateGasMeter) fork calleeH (Covered P) (Covered Q) :=
  (HoareUnder.meterCovers h ready (fun low hq => ends low hq.2) compat).consequence
    (fun _ hp => hp) fun _ ⟨low, ⟨stopped, hq⟩, covers⟩ => by
      obtain ⟨m, hm, rfl⟩ := covers.followsMeter_of_stopped stopped
      exact ⟨stopped, low, hq, ⟨m, hm, rfl⟩, covers.1⟩


end EthLib.Execution.Evm.Logic
