module

public import EthLib.Execution.Proofs.Evm.Call.StepRules
public import EthLib.Execution.Proofs.Rpc.Trace

/-!
# Proofs: the gas of consecutive entries of the opcode trace

Before Glamsterdam, take two consecutive entries at one depth.

The gas falls by the cost of the first, unless it is a call or a creation, or fails.

From Glamsterdam, the meter also holds a reservoir of state gas, which these proofs leave out.
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState)
open EthLib.Execution.Transactions

section Child

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- A call that sends a message sends it one level deeper than its caller. -/
private theorem callStep_child_depth {kind : CallKind} {evm caller : Evm fork Meter}
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
        dsimp only at h
        split at h
        · obtain ⟨_, -, hc⟩ := Base.map_ok_iff.mp h; cases hc
        · cases h; rfl
    · cases hc
  · cases hc

/-- A creation that sends a message sends it one level deeper than its caller. -/
private theorem createStep_child_depth {create2 : Bool} {evm caller : Evm fork Meter}
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

/-- A step that sends a message runs a call or a creation, and sends it one level deeper. -/
private theorem step_child {evm caller : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : step fork evm = .ok (.child caller message resume)) :
    message.depth = caller.message.depth + 1 ∧ evm.code.size ≠ 0 ∧
      mnemonicOf fork (stepOp evm) ∈
        ["CALL", "CALLCODE", "DELEGATECALL", "STATICCALL", "CREATE", "CREATE2"] := by
  unfold Evm.step at h
  split at h
  · rename_i hpc
    dsimp only at h
    split at h
    · cases h
    · rename_i op hop
      split at h
      · obtain ⟨_, -, hc⟩ := Base.map_ok_iff.mp h; cases hc
      · split at h
        · rename_i run hrun
          have hstep : stepOp evm = some op := by simp [stepOp, hpc, hop]
          rw [hstep]
          refine ⟨?_, by omega, ?_⟩
          · cases op <;> simp [messageInstruction, callInstruction, createInstruction,
              HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
            all_goals first
              | (subst hrun; first | exact callStep_child_depth h | exact createStep_child_depth h)
              | (obtain ⟨-, rfl⟩ := hrun; exact createStep_child_depth h)
              | (split at hrun <;> rename_i heq <;> split at heq <;> simp at heq hrun
                 subst heq hrun
                 exact callStep_child_depth h)
          · cases op <;> simp [messageInstruction, callInstruction, createInstruction,
              HOrElse.hOrElse, OrElse.orElse, Option.orElse, mnemonicOf, opMnemonic] at hrun ⊢
        · cases h
  · obtain ⟨_, -, hc⟩ := Base.map_ok_iff.mp h; cases hc

end Child

/-- The mnemonics of the steps that can start a message. -/
private abbrev messageOps : List String :=
  ["CALL", "CALLCODE", "DELEGATECALL", "STATICCALL", "CREATE", "CREATE2"]

/-- An entry that is no call or creation, and does not fail. -/
private def Plain (entry : StructLog) : Prop := entry.op ∉ messageOps ∧ entry.error = none

/-- Between two consecutive entries at one depth, the first plain, the gas falls by its cost. -/
private def Chained (logs : Array StructLog) : Prop :=
  ∀ i (hi : i + 1 < logs.size), logs[i].depth = logs[i + 1].depth → Plain logs[i] →
    logs[i + 1].gas + logs[i].gasCost = logs[i].gas

/-- The logger holds as many entries as the bound allows. -/
private def Full (config : TraceConfig) (tracer : Tracer) : Prop :=
  config.limit ≠ 0 ∧ config.limit ≤ tracer.logs.size

/-- The logger before a frame whose message has depth `m` steps with the gas `g`.

A plain last entry is no shallower than the frame.

At the depth of the frame, it falls to `g` by its cost, and the frame has code. -/
private def Before (config : TraceConfig) (tracer : Tracer) (m g : Nat) (code : Prop) : Prop :=
  Chained tracer.logs ∧ (Full config tracer ∨ ∀ entry, tracer.logs.back? = some entry →
    Plain entry → m + 1 ≤ entry.depth ∧
      (entry.depth = m + 1 → entry.gas = g + entry.gasCost ∧ code))

/-- The logger after a frame whose message has depth `m` ends.

A plain last entry is no shallower. -/
private def After (config : TraceConfig) (tracer : Tracer) (m : Nat) : Prop :=
  Chained tracer.logs ∧ (Full config tracer ∨ ∀ entry, tracer.logs.back? = some entry →
    Plain entry → m + 1 ≤ entry.depth)

/-- The logger before a message starts: its last entry is not plain. -/
private def Fresh (config : TraceConfig) (tracer : Tracer) : Prop :=
  Chained tracer.logs ∧ (Full config tracer ∨ ∀ entry, tracer.logs.back? = some entry →
    ¬Plain entry)

/-- One more entry keeps the chain when the last entry, if plain at its depth, falls to its gas. -/
private theorem chained_push {logs : Array StructLog} {entry : StructLog} (h : Chained logs)
    (last : ∀ prev, logs.back? = some prev → prev.depth = entry.depth → Plain prev →
      entry.gas + prev.gasCost = prev.gas) :
    Chained (logs.push entry) := by
  intro i hi hd hp
  simp only [Array.size_push] at hi
  by_cases lt : i + 1 < logs.size
  · simp only [Array.getElem_push_lt lt, Array.getElem_push_lt (Nat.lt_of_succ_lt lt)] at hd hp ⊢
    exact h i lt hd hp
  · have eq : i + 1 = logs.size := by omega
    have il : i < logs.size := by omega
    have hb : logs.back? = some logs[i] := by
      simp [Array.back?, show logs.size - 1 = i by omega, il]
    simp only [Array.getElem_push_lt il] at hd hp ⊢
    simp only [eq, Array.getElem_push_eq] at hd ⊢
    exact last _ hb hd hp

section Record

variable {fork : Fork} (config : TraceConfig)

/-- The logger either keeps its state, for a frame with no code or once full, or adds one entry. -/
private theorem record_cases (evm : Evm fork Nat) (result : Except EvmError (StepResult fork Nat))
    (tracer : Tracer) :
    (Tracer.record config evm result tracer = tracer ∧
      (evm.code.size = 0 ∨ Full config tracer)) ∨
    (evm.code.size ≠ 0 ∧ ¬Full config tracer ∧ ∃ entry : StructLog,
      (Tracer.record config evm result tracer).logs = tracer.logs.push entry ∧
      entry.gas = evm.gas ∧ entry.gasCost = stepCost evm result ∧
      entry.depth = evm.message.depth + 1 ∧ entry.error = stepError result ∧
      entry.op = mnemonicOf fork (stepOp evm)) := by
  unfold Tracer.record
  split
  · exact .inl ⟨rfl, by assumption⟩
  · rename_i hc
    refine .inr ⟨fun h => hc (.inl h), fun h => hc (.inr h), _, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A plain last entry at the depth of the frame falls to the gas of a new entry from it. -/
private theorem before_push {tracer : Tracer} {m g : Nat} {code : Prop} {entry : StructLog}
    (pre : Before config tracer m g code) (full : ¬Full config tracer)
    (depth : entry.depth = m + 1) (gas : entry.gas = g) : Chained (tracer.logs.push entry) := by
  refine chained_push pre.1 fun prev hb hd hp => ?_
  rcases pre.2 with f | p
  · exact absurd f full
  · have := (p prev hb hp).2 (hd.trans depth)
    omega

/-- A step to the next frame leaves the logger ready for the step of that frame. -/
private theorem before_next {evm after : Evm fork Nat} {tracer : Tracer}
    (pre : Before config tracer evm.message.depth evm.gas (evm.code.size ≠ 0))
    (message : after.message = evm.message) (code : after.code = evm.code)
    (gas : after.gas ≤ evm.gas) :
    Before config (Tracer.record config evm (.ok (.next after)) tracer) after.message.depth
      after.gas (after.code.size ≠ 0) := by
  rw [message, code]
  rcases record_cases config evm (.ok (.next after)) tracer with
    ⟨same, empty | full⟩ | ⟨nonempty, full, entry, logs, egas, cost, depth, -, -⟩
  · rw [same]
    refine ⟨pre.1, pre.2.imp id fun p prev hb hp => ?_⟩
    obtain ⟨le, eq⟩ := p prev hb hp
    exact ⟨le, fun hd => absurd empty (eq hd).2⟩
  · rw [same]
    exact ⟨pre.1, .inl full⟩
  · refine ⟨logs ▸ before_push config pre full depth egas, .inr fun prev hb _ => ?_⟩
    rw [logs, Array.back?_push] at hb
    cases hb
    refine ⟨Nat.le_of_eq depth.symm, fun _ => ⟨?_, nonempty⟩⟩
    simp only [cost, stepCost, GasMeter.gasLeft] at egas ⊢
    omega

/-- A step that fails leaves the logger as after the end of the frame. -/
private theorem after_error {evm : Evm fork Nat} {tracer : Tracer} {e : EvmError} {g : Nat}
    {code : Prop} (pre : Before config tracer evm.message.depth g code) (hg : evm.gas = g) :
    After config (Tracer.record config evm (.error e) tracer) evm.message.depth := by
  rcases record_cases config evm (.error e) tracer with
    ⟨same, -⟩ | ⟨-, full, entry, logs, egas, -, depth, err, -⟩
  · rw [same]
    exact ⟨pre.1, pre.2.imp id fun p prev hb hp => (p prev hb hp).1⟩
  · refine ⟨logs ▸ before_push config pre full depth (egas.trans hg), .inr fun prev hb hp => ?_⟩
    rw [logs, Array.back?_push] at hb
    cases hb
    simp [Plain, err, stepError] at hp

/-- A step that sends a message leaves the logger fresh for that message. -/
private theorem fresh_child {evm caller : Evm fork Nat} {message : Message fork}
    {resume : Evm fork Nat → Except EvmError (Evm fork Nat)} {tracer : Tracer} {g : Nat}
    {code : Prop} (h : step fork evm = .ok (.child caller message resume))
    (pre : Before config tracer evm.message.depth g code) (hg : evm.gas = g) :
    Fresh config (Tracer.record config evm (.ok (.child caller message resume)) tracer) := by
  obtain ⟨-, nonempty, op⟩ := step_child h
  rcases record_cases config evm (.ok (.child caller message resume)) tracer with
    ⟨same, empty | full⟩ | ⟨-, full, entry, logs, egas, -, depth, -, eop⟩
  · exact absurd empty nonempty
  · rw [same]
    exact ⟨pre.1, .inl full⟩
  · refine ⟨logs ▸ before_push config pre full depth (egas.trans hg), .inr fun prev hb hp => ?_⟩
    rw [logs, Array.back?_push] at hb
    cases hb
    exact hp.1 (eop ▸ op)

omit config in
/-- A fresh logger is ready for the first step of any frame. -/
private theorem Fresh.before {config : TraceConfig} {tracer : Tracer} (h : Fresh config tracer)
    (m g : Nat) (code : Prop) : Before config tracer m g code :=
  ⟨h.1, h.2.imp id fun p prev hb hp => absurd hp (p prev hb)⟩

omit config in
/-- A fresh logger is as after the end of any frame. -/
private theorem Fresh.after {config : TraceConfig} {tracer : Tracer} (h : Fresh config tracer)
    (m : Nat) : After config tracer m :=
  ⟨h.1, h.2.imp id fun p prev hb hp => absurd hp (p prev hb)⟩

omit config in
/-- A logger ready for a frame that stops is as after the end of that frame. -/
private theorem Before.after {config : TraceConfig} {tracer : Tracer} {m g : Nat} {code : Prop}
    (h : Before config tracer m g code) : After config tracer m :=
  ⟨h.1, h.2.imp id fun p prev hb hp => (p prev hb hp).1⟩

omit config in
/-- After the end of a child, the logger is ready for the next step of its caller. -/
private theorem After.before {config : TraceConfig} {tracer : Tracer} {m : Nat}
    (h : After config tracer (m + 1)) (g : Nat) (code : Prop) : Before config tracer m g code :=
  ⟨h.1, h.2.imp id fun p prev hb hp =>
    ⟨by have := p prev hb hp; omega, fun hd => by have := p prev hb hp; omega⟩⟩

omit config in
/-- After the end of a child, the logger is as after the end of its caller. -/
private theorem After.up {config : TraceConfig} {tracer : Tracer} {m : Nat}
    (h : After config tracer (m + 1)) : After config tracer m :=
  ⟨h.1, h.2.imp id fun p prev hb hp => by have := p prev hb hp; omega⟩

end Record

section Run

variable {fork : Fork} (config : TraceConfig)

/-- The match on a resumed frame takes its error branch on an error. -/
private theorem resume_match_error {β : Sort _} {x : Except EvmError (Evm fork Nat)}
    {e : EvmError} (h : x = .error e) (h_1 : (e : EvmError) → x = .error e → β)
    (h_2 : (after : Evm fork Nat) → x = .ok after → β) :
    runFrameWith.match_1 (fun _ => β) x h_1 h_2 = h_1 e h :=
  eq_of_heq (runFrameWith.match_1.congr_eq_1 _ _ _ _ e h)

/-- The match on a resumed frame takes its success branch on a frame. -/
private theorem resume_match_ok {β : Sort _} {x : Except EvmError (Evm fork Nat)}
    {after : Evm fork Nat} (h : x = .ok after) (h_1 : (e : EvmError) → x = .error e → β)
    (h_2 : (after : Evm fork Nat) → x = .ok after → β) :
    runFrameWith.match_1 (fun _ => β) x h_1 h_2 = h_2 after h :=
  eq_of_heq (runFrameWith.match_1.congr_eq_2 _ _ _ _ after h)

/-- A logged run of a frame leaves the logger as after the end of that frame.

The logger must be ready for the step of the frame.

Each message that the frame sends must leave a fresh logger as after the end of the message. -/
private theorem runFrameWith_after
    {decreases : ∀ {evm : Evm fork Nat} {result : StepResult fork Nat}, evm.running = true →
      step fork evm = .ok result → result.Decreases evm}
    {bound : Nat} {runChild : MessageRunnerIn (StateT Tracer (Except EvmError)) fork Nat bound}
    (children : ∀ caller message lt tracer r tracer',
      runChild caller message lt tracer = .ok (r, tracer') → Fresh config tracer →
        After config tracer' message.depth)
    (evm : Evm fork Nat) (within : GasMeter.gasHeld evm.gas ≤ bound) (tracer : Tracer)
    {r : { after : Evm fork Nat // GasMeter.gasHeld after.gas ≤ bound }} {tracer' : Tracer}
    (h : runFrameWith (fun evm result => modify (Tracer.record config evm result)) (step fork)
      decreases bound runChild evm within tracer = .ok (r, tracer'))
    (pre : Before config tracer evm.message.depth evm.gas (evm.code.size ≠ 0)) :
    After config tracer' evm.message.depth := by
  induction hm : measure evm using Nat.strongRecOn generalizing evm tracer with
  | _ n ih =>
  subst hm
  generalize hrun : runFrameWith (fun evm result => modify (Tracer.record config evm result))
    (step fork) decreases bound runChild evm within = run at h
  rw [runFrameWith] at hrun
  by_cases running : evm.running
  · simp only [running, dite_true] at hrun
    split at hrun <;> rename_i hs <;> subst hrun
    · rename_i e
      by_cases aborts : e.aborts <;>
        simp [aborts, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure, modify,
          modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, throw, throwThe,
          MonadExceptOf.throw, StateT.lift] at h
      obtain ⟨-, rfl⟩ := h
      exact after_error config pre rfl
    · simp only [bind, StateT.bind, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, pure, Except.bind, Except.pure] at h
      have keep := (stepRules_messageCode (fork := fork) (Meter := Nat)).step hs
      have lower := decreases running hs
      have := ih _ lower _ _ _ h
        (before_next config pre keep.1 keep.2 (gasHeld_le_of_measure_lt lower)) rfl
      rwa [keep.1] at this
    · rename_i caller message resume
      simp only [bind, StateT.bind, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, pure, Except.bind, Except.pure] at h
      generalize Nat.lt_of_lt_of_le (decreases running hs).1 within = lt at h
      have fresh := fresh_child config hs pre rfl
      cases hr : runChild caller message lt
          (Tracer.record config evm (.ok (.child caller message resume)) tracer) with
      | error e =>
        rw [hr] at h
        cases h
      | ok a =>
        obtain ⟨⟨child, used⟩, mid⟩ := a
        have post := children _ _ _ _ _ _ hr fresh
        rw [hr] at h
        dsimp only at h
        have keep := ((stepRules_messageCode (fork := fork) (Meter := Nat)).step hs).1.1
        rw [(step_child hs).1, keep] at post
        cases hres : resume child with
        | error e =>
          rw [resume_match_error hres] at h
          by_cases aborts : e.aborts <;>
            simp [aborts, pure, StateT.pure, throw, throwThe, MonadExceptOf.throw,
              StateT.lift, Except.pure] at h
          · cases h
          · rw [← h.2]
            exact post.up
        | ok after =>
          rw [resume_match_ok hres] at h
          have same := sameContext_of_step_eq_child hs hres
          have message : after.message = evm.message :=
            same.message.trans ((message_incorporateChild _ _).trans keep)
          have := ih _ ((decreases running hs).2 child after used hres) _ _ _ h
            (message ▸ post.before _ _) rfl
          rwa [message] at this
  · simp only [running] at hrun
    subst hrun
    cases h
    exact pre.after

/-- A map that succeeds comes from a run that succeeds with the same state. -/
private theorem map_ok {α β : Type} {f : α → β} {x : StateT Tracer (Except EvmError) α}
    {s s' : Tracer} {b : β} (h : (f <$> x) s = .ok (b, s')) : ∃ a, x s = .ok (a, s') := by
  simp only [Functor.map, StateT.map] at h
  cases hx : x s with
  | error e => simp [hx, bind, Except.bind] at h
  | ok p =>
    simp only [hx, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨p.1, by rw [← h.2]⟩

/-- A bind that succeeds runs its first part, then the rest from the state it leaves. -/
private theorem bind_ok {α β : Type} {x : StateT Tracer (Except EvmError) α}
    {f : α → StateT Tracer (Except EvmError) β} {s s' : Tracer} {b : β}
    (h : (x >>= f) s = .ok (b, s')) : ∃ a mid, x s = .ok (a, mid) ∧ f a mid = .ok (b, s') := by
  simp only [bind, StateT.bind] at h
  cases hx : x s with
  | error e => simp [hx, Except.bind] at h
  | ok p => exact ⟨p.1, p.2, rfl, by simpa [hx, Except.bind] using h⟩

/-- A lifted result leaves the state as it is. -/
private theorem liftExcept_ok {α : Type} {x : Except EvmError α} {a : α} {s s' : Tracer}
    (h : (liftExcept x : StateT Tracer (Except EvmError) α) s = .ok (a, s')) : s' = s := by
  cases x <;> simp_all [liftExcept, throw, throwThe, MonadExceptOf.throw, StateT.lift,
    pure, StateT.pure, bind, Except.bind, Except.pure]

/-- A pure result leaves the state as it is. -/
private theorem pure_ok {α : Type} {a b : α} {s s' : Tracer}
    (h : (pure b : StateT Tracer (Except EvmError) α) s = .ok (a, s')) : s' = s := by
  simp_all [pure, StateT.pure, Except.pure]

/-- The match on a precompile run leaves the state as it is when both branches are pure. -/
private theorem precompile_state {β : Type} {x : Option (Evm fork Nat)}
    {h_1 : (after : Evm fork Nat) → x = some after → StateT Tracer (Except EvmError) β}
    {h_2 : x = none → StateT Tracer (Except EvmError) β}
    (p1 : ∀ after e, ∃ v, h_1 after e = pure v) (p2 : ∀ e, ∃ v, h_2 e = pure v)
    {s s' : Tracer} {b : β}
    (h : processMessageWith.match_1 fork (fun _ => StateT Tracer (Except EvmError) β) x h_1 h_2 s =
      .ok (b, s')) : s' = s := by
  cases x with
  | none =>
    obtain ⟨v, hv⟩ := p2 rfl
    rw [show processMessageWith.match_1 fork (fun _ => StateT Tracer (Except EvmError) β) none
      h_1 h_2 = h_2 rfl from rfl, hv] at h
    exact pure_ok h
  | some a =>
    obtain ⟨v, hv⟩ := p1 a rfl
    rw [show processMessageWith.match_1 fork (fun _ => StateT Tracer (Except EvmError) β) (some a)
      h_1 h_2 = h_1 a rfl from rfl, hv] at h
    exact pure_ok h

/-- The match on a deposit of code leaves the state as it is when it succeeds. -/
private theorem deposit_state {β : Type} {x : Except EvmError (Evm fork Nat)}
    {h_1 : (e : EvmError) → x = .error e → StateT Tracer (Except EvmError) β}
    {h_2 : (after : Evm fork Nat) → x = .ok after → StateT Tracer (Except EvmError) β}
    (p1 : ∀ e he, h_1 e he = throw e) (p2 : ∀ after he, ∃ v, h_2 after he = pure v)
    {s s' : Tracer} {b : β}
    (h : processCreateMessageWith.match_1 fork (fun _ => StateT Tracer (Except EvmError) β) x
      h_1 h_2 s = .ok (b, s')) : s' = s := by
  cases x with
  | error e =>
    rw [show processCreateMessageWith.match_1 fork (fun _ => StateT Tracer (Except EvmError) β)
      (.error e) h_1 h_2 = h_1 e rfl from rfl, p1] at h
    simp [throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, Except.bind] at h
  | ok a =>
    obtain ⟨v, hv⟩ := p2 a rfl
    rw [show processCreateMessageWith.match_1 fork (fun _ => StateT Tracer (Except EvmError) β)
      (.ok a) h_1 h_2 = h_2 a rfl from rfl, hv] at h
    exact pure_ok h

/-- A logged run of a message or a creation leaves a fresh logger as after its end.

The message has gas `n`, the measure of the induction. -/
private theorem process_after (n : Nat) :
    ∀ message : Message fork, message.gas = n →
      (∀ state substate (meter : Nat) held tracer r tracer',
        processMessageWith (M := StateT Tracer (Except EvmError)) fork
          (fun evm result => modify (Tracer.record config evm result)) message state substate
          meter held tracer = .ok (r, tracer') →
        Fresh config tracer → After config tracer' message.depth) ∧
      (∀ state substate (meter : Nat) held tracer r tracer',
        processCreateMessageWith (M := StateT Tracer (Except EvmError)) fork
          (fun evm result => modify (Tracer.record config evm result)) message state substate
          meter held tracer = .ok (r, tracer') →
        Fresh config tracer → After config tracer' message.depth) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro message gas
  have call : ∀ state substate (meter : Nat) held tracer r tracer',
      processMessageWith (M := StateT Tracer (Except EvmError)) fork
        (fun evm result => modify (Tracer.record config evm result)) message state substate
        meter held tracer = .ok (r, tracer') →
      Fresh config tracer → After config tracer' message.depth := by
    intro state substate meter held tracer r tracer' h fresh
    rw [processMessageWith] at h
    obtain ⟨_, h⟩ := map_ok h
    dsimp only at h
    by_cases ht : message.shouldTransferValue = true ∧ message.value ≠ 0
    all_goals
      first | simp only [ite_eq_left ht] at h | simp only [ite_eq_right ht] at h
      obtain ⟨_, mid, h1, hj⟩ := bind_ok h
      first | obtain rfl := liftExcept_ok h1 | obtain rfl := pure_ok h1
      cases hp : precompileAddress fork message with
      | some address =>
        simp only [hp] at hj
        by_cases hd : message.disablePrecompiles = true
        · simp only [hd, ite_true] at hj
          obtain rfl := pure_ok hj
          exact fresh.after _
        · simp only [hd] at hj
          obtain rfl := precompile_state (fun _ _ => ⟨_, rfl⟩) (fun _ => ⟨_, rfl⟩) hj
          exact fresh.after _
      | none =>
        simp only [hp] at hj
        refine runFrameWith_after config (fun caller child lt t r t' hr hf => ?_) _ _ _ hj
          (fresh.before _ _ _)
        have lt' : child.gas < n := gas ▸ lt
        cases hc : child.target <;> simp only [hc] at hr
        · exact (ih _ lt' child rfl).2 _ _ _ _ _ _ _ hr hf
        · exact (ih _ lt' child rfl).1 _ _ _ _ _ _ _ hr hf
  refine ⟨call, fun state substate meter held tracer r tracer' h fresh => ?_⟩
  rw [processCreateMessageWith] at h
  obtain ⟨_, mid, h1, hrest⟩ := bind_ok h
  obtain rfl := liftExcept_ok h1
  obtain ⟨⟨evm, used⟩, mid', h2, hdep⟩ := bind_ok hrest
  have post := call _ _ _ _ _ _ _ h2 fresh
  dsimp only at hdep
  obtain rfl := deposit_state (fun _ _ => rfl) (fun _ _ => ⟨_, rfl⟩) hdep
  exact post

/-- A logged message of a transaction keeps the chain of a fresh logger. -/
private theorem processMessageCallWith_chained (chainId : Nat) (message : Message fork)
    (state : State.TransactionState) (substate : Substate) (auths : List Authorization)
    (paid : Std.ExtTreeSet Address) {tracer tracer' : Tracer} {output : CallOutput}
    (h : processMessageCallWith (Meter := Nat) (M := StateT Tracer (Except EvmError))
      (fun evm result => modify (Tracer.record config evm result)) chainId message state
      substate auths paid tracer = .ok (output, tracer'))
    (fresh : Fresh config tracer) : Chained tracer'.logs := by
  rw [processMessageCallWith] at h
  revert h
  rcases prepareFirstFrame (Meter := Nat) chainId message state substate auths paid with
    ⟨e, read⟩ | first <;> intro h
  · by_cases aborts : e.aborts
    · simp [aborts, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, Except.bind] at h
    · simp only [aborts] at h
      obtain rfl := pure_ok h
      exact fresh.1
  · revert h
    cases message.target <;> intro h <;> dsimp only at h
    all_goals
      obtain ⟨⟨evm, used⟩, mid, h1, h2⟩ := bind_ok h
      obtain rfl := pure_ok h2
      first
        | exact ((process_after config _ _ rfl).1 _ _ _ _ _ _ _ h1 fresh).1
        | exact ((process_after config _ _ rfl).2 _ _ _ _ _ _ _ h1 fresh).1

end Run

/-- Before Glamsterdam, between two entries at one depth, the gas falls by the cost of the first.

The first entry must not be a call or a creation.

The gas that a message leaves unused comes back to the frame before its next entry.

It must not fail either, since a failed step ends its frame. -/
theorem traceRun_gas {fork : Fork} (config : TraceConfig) (early : fork < .glamsterdam)
    {env : BlockEnvironment fork} {block : BlockState} {included : Included}
    {tx : Transaction} {precompiles : Address → Option Address} {lifted : LiftedRules}
    {output : TransactionOutput} {tracer : Tracer}
    (h : traceRun config env block included tx precompiles lifted = .ok (output, tracer))
    (i : Nat) (hi : i + 1 < tracer.logs.size)
    (depth : tracer.logs[i].depth = tracer.logs[i + 1].depth)
    (plain : tracer.logs[i].op ∉
      ["CALL", "CALLCODE", "DELEGATECALL", "STATICCALL", "CREATE", "CREATE2"])
    (ok : tracer.logs[i].error = none) :
    tracer.logs[i + 1].gas + tracer.logs[i].gasCost = tracer.logs[i].gas := by
  have fresh : Fresh config {} := ⟨fun i hi => by simp at hi, .inr fun _ hb => by simp at hb⟩
  unfold traceRun at h
  have specified : ¬Fork.hegota ≤ fork := fun hh =>
    Nat.not_le_of_lt early (Nat.le_trans (by decide : Fork.glamsterdam ≤ .hegota) hh)
  have pre : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt early
  rw [processTransactionWith, ite_eq_right specified, ite_eq_right pre, runTransactionWith] at h
  obtain ⟨_, t1, h1, h⟩ := bind_ok h
  obtain rfl := liftExcept_ok h1
  obtain ⟨_, t2, h2, h⟩ := bind_ok h
  obtain rfl := liftExcept_ok h2
  obtain ⟨_, t3, h3, h⟩ := bind_ok h
  obtain rfl := liftExcept_ok h3
  obtain ⟨_, t4, h4, h⟩ := bind_ok h
  have chained := processMessageCallWith_chained config _ _ _ _ _ _ h4 fresh
  dsimp only at h
  obtain ⟨⟨_, _⟩, t5, h5, h6⟩ := bind_ok h
  obtain rfl := liftExcept_ok h5
  dsimp only at h6
  obtain ⟨_, t7, h7, h8⟩ := bind_ok h6
  obtain rfl := liftExcept_ok h7
  obtain rfl := pure_ok h8
  exact chained i hi depth ⟨plain, ok⟩

end EthLib.Execution.Rpc
