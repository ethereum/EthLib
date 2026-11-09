module

public import EthLib.Execution.Proofs.Evm.Logic.Fault
public import EthLib.Execution.Proofs.Evm.Logic.Rules

/-!
# Proofs: runs with less gas

A run with less gas follows the run with more gas, or it fails.

The facts here are for the meter of one counter of gas, the meter of every fork before Glamsterdam.

At a later fork they hold of that meter, not of the meter of the fork.

A frame with `k` more gas is the same frame, with `k` added to its gas.

An instruction is monotone in gas when, on every frame, it fails, or it gives a frame `b`.

In that second case, the instruction on the frame with `k` more gas gives `b` with `k` more gas.

A frame is monotone in gas when the same holds of the step from every frame with less gas than it.

The triples here are over the steps from frames that are monotone in gas.

Each such triple is a triple over the steps of the logic.

A specification of this kind from a frame with `k` more gas also says how the frame itself ends.

Say the loop of the interpreter runs the frame to a stopped frame with no error.

Then that stopped frame, with `k` more gas, meets the postcondition.

So a run with less gas that succeeds ends as the specification says, with exactly `k` less gas.

A frame is stuck when it is running and the step from it, and from it with any less gas, fails.

These steps may reach a stuck frame from a frame with `k` more gas than a frame `l`.

Then the run of `l` does not end with no error.

GAS is not monotone in gas, since it pushes the gas left.

A step that sends a message, as a call or a creation does, is no step of the logic.

So no fact here covers the calls and the creations.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)

variable {fork : Fork}

/-- The frame `evm` with `k` more gas, with the one-counter meter. -/
def addGas (k : Nat) (evm : Evm fork Nat) : Evm fork Nat := { evm with gas := evm.gas + k }

@[simp] theorem gas_addGas (k : Nat) (evm : Evm fork Nat) : (addGas k evm).gas = evm.gas + k :=
  rfl

@[simp] theorem running_addGas (k : Nat) (evm : Evm fork Nat) :
    (addGas k evm).running = evm.running := rfl

@[simp] theorem error_addGas (k : Nat) (evm : Evm fork Nat) : (addGas k evm).error = evm.error :=
  rfl

@[simp] theorem addGas_zero (evm : Evm fork Nat) : addGas 0 evm = evm := rfl

/-- A result of an instruction that is no success: an error, or a stopped frame with an error. -/
def Fails (r : Except EvmError (Evm fork Nat)) : Prop :=
  (∃ e, r = .error e) ∨ ∃ b, r = .ok b ∧ b.running = false ∧ b.error ≠ none

/-- The result `lo` fails, or it is a frame `b` and the result `hi` is `b` with `k` more gas. -/
def Follows (k : Nat) (lo hi : Except EvmError (Evm fork Nat)) : Prop :=
  Fails lo ∨ ∃ b, lo = .ok b ∧ hi = .ok (addGas k b)

/-- An instruction that, on every frame, fails, or follows its result on that frame with more gas.

The frame with more gas then gives the same result with the same more gas. -/
def RunMono (run : Evm fork Nat → Except EvmError (Evm fork Nat)) : Prop :=
  ∀ evm k, Follows k (run evm) (run (addGas k evm))

/-- A result of a step that is no success: an error, or a stopped frame with an error. -/
def StepFails (r : Except EvmError (StepResult fork Nat)) : Prop :=
  (∃ e, r = .error e) ∨ ∃ b, r = .ok (.next b) ∧ b.running = false ∧ b.error ≠ none

/-- The result `lo` of a step fails, or it is a frame `b`, and `hi` is `b` with `k` more gas. -/
def StepFollows (k : Nat) (lo hi : Except EvmError (StepResult fork Nat)) : Prop :=
  StepFails lo ∨ ∃ b, lo = .ok (.next b) ∧ hi = .ok (.next (addGas k b))

/-- From every frame with `k` less gas than `evm`, the step fails, or it follows that of `evm`. -/
def GasMono (evm : Evm fork Nat) : Prop :=
  ∀ k low, evm = addGas k low → StepFollows k (step fork low) (step fork evm)

/-- A step of the logic from a frame that is monotone in gas. -/
def StepG (fork : Fork) (evm after : Evm fork Nat) : Prop := Step fork evm after ∧ GasMono evm

/-- A triple over the steps from frames that are monotone in gas. -/
abbrev HoareG (fork : Fork) (P Q : Evm fork Nat → Prop) : Prop := Triple (StepG fork) P Q

/-- A specification over the steps from frames that are monotone in gas. -/
def SpecG (fork : Fork) (P Q : Evm fork Nat → Prop) : Prop :=
  HoareG fork P fun evm => evm.running = false ∧ Q evm

/-! ## From instructions to steps -/

/-- An instruction result that follows another gives step results that follow. -/
theorem Follows.next {k : Nat} {lo hi : Except EvmError (Evm fork Nat)} (h : Follows k lo hi) :
    StepFollows k (StepResult.next <$> lo) (StepResult.next <$> hi) := by
  rcases h with (⟨e, rfl⟩ | ⟨b, rfl, hr, he⟩) | ⟨b, rfl, rfl⟩
  · exact .inl (.inl ⟨e, rfl⟩)
  · exact .inl (.inr ⟨b, rfl, hr, he⟩)
  · exact .inr ⟨b, rfl, rfl⟩

/-- A frame at an opcode whose instruction is monotone in gas is monotone in gas. -/
theorem gasMono_of_run {evm : Evm fork Nat} {op : Op}
    {run : Evm fork Nat → Except EvmError (Evm fork Nat)} (hlt : evm.pc < evm.code.size)
    (decoded : Op.ofByte fork evm.code[evm.pc] = some op) (hrun : instruction fork op = some run)
    (mono : RunMono run) : GasMono evm := by
  rintro k low rfl
  rw [step_of_instruction (evm := low) hlt decoded hrun,
    step_of_instruction (evm := addGas k low) hlt decoded hrun]
  exact (mono low k).next

/-- A frame at a byte that is no opcode at the fork is monotone in gas, since both steps fail. -/
theorem gasMono_of_none {evm : Evm fork Nat} (hlt : evm.pc < evm.code.size)
    (none : Op.ofByte fork evm.code[evm.pc] = none) : GasMono evm := by
  rintro k low rfl
  exact .inl (.inl ⟨_, step_of_ofByte_eq_none (evm := low) hlt none⟩)

/-! ## Triples over the steps from frames that are monotone in gas -/

/-- A triple over the steps from frames that are monotone in gas is a triple over the steps. -/
theorem HoareG.toHoare {P Q : Evm fork Nat → Prop} (h : HoareG fork P Q) : Hoare fork P Q :=
  fun evm hp =>
    let ⟨after, hr, hq⟩ := h evm hp
    ⟨after, hr.mono And.left, hq⟩

/-- A specification over the steps from frames that are monotone in gas is a specification. -/
theorem SpecG.toSpec {P Q : Evm fork Nat → Prop} (h : SpecG fork P Q) : Spec fork P Q :=
  HoareG.toHoare h

/-- A triple to a frame from which the specification holds. -/
theorem SpecG.seq {P Q R : Evm fork Nat → Prop} (first : HoareG fork P Q)
    (second : SpecG fork Q R) : SpecG fork P R := Triple.seq first second

/-- Consequence for a specification over the steps from frames that are monotone in gas. -/
theorem SpecG.consequence {P P' Q Q' : Evm fork Nat → Prop} (h : SpecG fork P Q)
    (pre : ∀ evm, P' evm → P evm) (post : ∀ evm, Q evm → Q' evm) : SpecG fork P' Q' :=
  Triple.consequence h pre fun evm ⟨hs, hq⟩ => ⟨hs, post evm hq⟩

/-- From a frame of the precondition, the loop of the interpreter gives one of the postcondition.

It holds for every bound on the gas of messages and every runner of messages. -/
theorem SpecG.runFrame {P Q : Evm fork Nat → Prop} (h : SpecG fork P Q)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (hp : P evm) (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ Q stopped :=
  Spec.runFrame (SpecG.toSpec h) hp within

variable {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}
  {returnData : ByteArray}

/-- The rule of an opcode whose instruction is monotone in gas.

It comes from the instruction that its byte runs on a frame of the code. -/
theorem At.ruleG {byte : UInt8} {op : Op}
    {run : Evm fork Nat → Except EvmError (Evm fork Nat)} {post : Evm fork Nat → Prop}
    (hlt : pc < code.size) (hbyte : code[pc] = byte) (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction fork op = some run) (mono : RunMono run)
    (h : ∀ evm, At code message pc stack memory gas state substate returnData evm →
      ∃ after, run evm = .ok after ∧ post after) :
    HoareG fork (At code message pc stack memory gas state substate returnData) post := by
  apply Triple.of_step
  intro evm hp
  obtain ⟨after, ok, hpost⟩ := h evm hp
  refine ⟨after, ⟨Step.of_code hp.2.2.2.2.2.2.2.1 hp.1 hp.2.2.2.1 hlt hbyte decoded hrun ok, ?_⟩,
    hpost⟩
  obtain ⟨hcode, -, -, hpc, -⟩ := hp
  subst hcode hpc
  exact gasMono_of_run hlt (by rw [hbyte]; exact decoded) hrun mono

/-- A byte that is no opcode at the fork halts the frame with that byte as an invalid opcode. -/
theorem invalidG {byte : UInt8} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (none : Op.ofByte fork byte = none) :
    SpecG fork (At code message pc stack memory gas state substate returnData)
      (Faulted (.invalidOpcode byte) state substate) := by
  apply Triple.of_step
  intro evm hat
  obtain ⟨hcode, -, -, hpc, -, -, -, hrun, -, -, hs, hss, -⟩ := hat
  subst hcode hpc
  have hnone : Op.ofByte fork evm.code[evm.pc] = .none := by rw [hbyte]; exact none
  have hstep : step fork evm = .error (.invalidOpcode byte) := by
    rw [step_of_ofByte_eq_none hlt hnone, hbyte]
  exact ⟨_, ⟨Step.halt hrun hstep rfl, gasMono_of_none hlt hnone⟩,
    rfl, rfl, rfl, rfl, rfl, hs, hss⟩

/-- A frame of a code with some gas, with `k` more gas, is the frame of the code with `k` more. -/
theorem At.addGas {evm : Evm fork Nat}
    (h : At code message pc stack memory gas state substate returnData evm) (k : Nat) :
    At code message pc stack memory (gas + k) state substate returnData (addGas k evm) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, by simp [h7], h8, h9, h10, h11, h12, h13⟩

/-! ## A run with less gas -/

section Loop

variable {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- A running frame whose step fails does not run to a frame with no error in the loop. -/
theorem error_ne_none_of_stepFails {low s : Evm fork Nat} (running : low.running = true)
    (fails : StepFails (step fork low)) {within : GasMeter.gasHeld low.gas ≤ bound}
    (hs : runFrame (step fork) (step_decreases fork) bound runChild low within = .ok s) :
    s.error ≠ none := by
  rcases fails with ⟨e, he⟩ | ⟨b, hb, hbr, hbe⟩
  · cases ab : e.aborts
    · rw [runFrame_of_step_eq_error running he ab] at hs
      cases hs
      simp [exceptionalHalt]
    · rw [runFrame_of_step_eq_abort running he ab] at hs
      cases hs
  · rw [runFrame_of_step_eq_next running hb, runFrame_of_running_eq_false hbr] at hs
    cases hs
    exact hbe

/-- A chain of steps from frames monotone in gas, from `l` with `k` more gas to a stopped `z`.

When the loop runs `l` to a frame `s` with no error, `z` is `s` with `k` more gas. -/
theorem low_of_reaches {hi z : Evm fork Nat} (hr : Reaches (StepG fork) hi z)
    (hz : z.running = false) :
    ∀ (k : Nat) (low : Evm fork Nat), hi = addGas k low →
      ∀ (within : GasMeter.gasHeld low.gas ≤ bound) {s : Evm fork Nat},
        runFrame (step fork) (step_decreases fork) bound runChild low within = .ok s →
        s.error = none → z = addGas k s := by
  induction hr with
  | refl =>
    rintro k low rfl within s hs -
    rw [runFrame_of_running_eq_false (by simpa using hz)] at hs
    cases hs
    rfl
  | step hstep _ ih =>
    rintro k low rfl within s hs hok
    obtain ⟨hstep, mono⟩ := hstep
    have running : low.running = true := by simpa using hstep.running
    rcases mono k low rfl with fails | ⟨b, hb, hh⟩
    · exact absurd hok (error_ne_none_of_stepFails running fails hs)
    · rw [runFrame_of_step_eq_next running hb] at hs
      cases hstep with
      | next _ hn =>
        rw [hh] at hn
        cases hn
        exact ih hz k b rfl _ hs hok
      | halt _ hn _ =>
        rw [hh] at hn
        cases hn

/-- A specification over steps from frames monotone in gas, from `l` with `k` more gas.

When the loop runs `l` to a frame `s` with no error, `s` with `k` more gas meets the postcondition.
-/
theorem SpecG.low {P Q : Evm fork Nat → Prop} (h : SpecG fork P Q) {k : Nat} {l : Evm fork Nat}
    (hp : P (addGas k l)) (within : GasMeter.gasHeld l.gas ≤ bound) {s : Evm fork Nat}
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild l within = .ok s)
    (hok : s.error = none) : Q (addGas k s) := by
  obtain ⟨z, hr, hz, hq⟩ := h _ hp
  rw [← low_of_reaches hr hz k l rfl within hs hok]
  exact hq

/-- A specification to a normal halt, from a frame with `k` more gas than the frame `l`.

When the loop runs `l` to a frame `s` with no error, `s` is that halt with `k` less gas. -/
theorem SpecG.halted {out : ByteArray} {gas' : Nat} {state' : State.TransactionState}
    {substate' : Substate} {k : Nat}
    (h : SpecG fork (At code message pc stack memory (gas + k) state substate returnData)
      (Halted false out gas' state' substate'))
    {l : Evm fork Nat} (hl : At code message pc stack memory gas state substate returnData l)
    (within : GasMeter.gasHeld l.gas ≤ bound) {s : Evm fork Nat}
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild l within = .ok s)
    (hok : s.error = none) :
    s.running = false ∧ s.output = out ∧ s.gas + k = gas' ∧ s.state = state' ∧
      s.substate = substate' := by
  obtain ⟨hr, -, ho, hg, hst, hss⟩ := SpecG.low h (hl.addGas k) within hs hok
  exact ⟨hr, ho, hg, hst, hss⟩

/-- A specification to frames with an error, from `l` with `k` more gas.

The loop then runs `l` to no frame with no error. -/
theorem SpecG.not_ok {P Q : Evm fork Nat → Prop} (h : SpecG fork P Q)
    (herr : ∀ evm, Q evm → evm.error ≠ none) {k : Nat} {l : Evm fork Nat} (hp : P (addGas k l))
    (within : GasMeter.gasHeld l.gas ≤ bound) {s : Evm fork Nat}
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild l within = .ok s) :
    s.error ≠ none := by
  intro hok
  exact herr _ (SpecG.low h hp within hs hok) (by simpa using hok)

/-! ## Stuck frames -/

/-- A running frame from which the step fails, and from it with any less gas. -/
def Stuck (evm : Evm fork Nat) : Prop :=
  evm.running = true ∧ ∀ k low, evm = addGas k low → StepFails (step fork low)

/-- A chain of steps from frames monotone in gas, from `l` with `k` more gas to a stuck frame.

The loop then runs `l` to no frame with no error. -/
theorem not_ok_of_reaches {hi z : Evm fork Nat} (hr : Reaches (StepG fork) hi z) (hz : Stuck z) :
    ∀ (k : Nat) (low : Evm fork Nat), hi = addGas k low →
      ∀ (within : GasMeter.gasHeld low.gas ≤ bound) {s : Evm fork Nat},
        runFrame (step fork) (step_decreases fork) bound runChild low within = .ok s →
        s.error ≠ none := by
  induction hr with
  | refl =>
    rintro k low rfl within s hs
    exact error_ne_none_of_stepFails (by simpa using hz.1) (hz.2 k low rfl) hs
  | step hstep _ ih =>
    rintro k low rfl within s hs
    obtain ⟨hstep, mono⟩ := hstep
    have running : low.running = true := by simpa using hstep.running
    rcases mono k low rfl with fails | ⟨b, hb, hh⟩
    · exact error_ne_none_of_stepFails running fails hs
    · rw [runFrame_of_step_eq_next running hb] at hs
      cases hstep with
      | next _ hn =>
        rw [hh] at hn
        cases hn
        exact ih hz k b rfl _ hs
      | halt _ hn _ =>
        rw [hh] at hn
        cases hn

/-- A frame that, with any gas from `B` on, reaches a stuck frame by steps monotone in gas.

The loop runs it, with any gas, to no frame with no error. -/
theorem no_ok_stuck {B : Nat}
    (h : ∀ g, B ≤ g →
      HoareG fork (At code message pc stack memory g state substate returnData) Stuck)
    {evm s : Evm fork Nat}
    (start : At code message pc stack memory gas state substate returnData evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hs : runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    s.error ≠ none := by
  obtain ⟨z, hr, hz⟩ := h (gas + B) (Nat.le_add_left B gas) _ (start.addGas B)
  exact not_ok_of_reaches hr hz B evm rfl within hs

/-- A frame that, with its own gas, reaches a stuck frame by steps monotone in gas.

The loop runs it to no frame with no error. -/
theorem no_ok_stuck_at
    (h : HoareG fork (At code message pc stack memory gas state substate returnData) Stuck)
    {evm s : Evm fork Nat}
    (start : At code message pc stack memory gas state substate returnData evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hs : runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    s.error ≠ none := by
  obtain ⟨z, hr, hz⟩ := h evm start
  exact not_ok_of_reaches hr hz 0 evm (addGas_zero evm).symm within hs

end Loop

end EthLib.Execution.Evm.Logic
