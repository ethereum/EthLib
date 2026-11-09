module

public import EthLib.Execution.Proofs.Evm.Logic.Fault

/-!
# Proofs: runs with less gas

By steps that are monotone in gas, a run with less gas follows the run with more gas, or it fails.

A run that reverts fails too, so these facts say nothing of its gas.

The facts here are for the meter of one counter of gas, the meter of every fork before Glamsterdam.

Take a specification over such steps, from a frame with `k` more gas than a frame `l`.

Say the loop of the interpreter runs `l` to a stopped frame with no error.

Then that stopped frame, with `k` more gas, meets the postcondition.

So a run with less gas that succeeds ends as the specification says, with exactly `k` less gas.

A frame is stuck when it is running and the step from it, and from it with any less gas, fails.

Say such steps reach a stuck frame from a frame with `k` more gas than a frame `l`.

Then every frame that the loop runs `l` to has an error.

GAS is not monotone in gas, and a step that sends a message is no step of the logic.

So no fact here covers GAS, the calls and the creations.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)

variable {fork : Fork}

variable {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}
  {returnData : ByteArray}

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

/-- A chain of steps from frames monotone in gas, from `low` with `k` more gas to `z`.

When the loop runs `low` to a frame `s` with no error, `z` is a frame `m` with `k` more gas.

The loop runs `m` to `s` too. -/
theorem reaches_low {hi z : Evm fork Nat} (hr : Reaches (StepG fork) hi z) :
    ∀ (k : Nat) (low : Evm fork Nat), hi = addGas k low →
      ∀ (within : GasMeter.gasHeld low.gas ≤ bound) {s : Evm fork Nat},
        runFrame (step fork) (step_decreases fork) bound runChild low within = .ok s →
        s.error = none → ∃ m within', z = addGas k m ∧
          runFrame (step fork) (step_decreases fork) bound runChild m within' = .ok s := by
  induction hr with
  | refl =>
    rintro k low rfl within s hs -
    exact ⟨low, within, rfl, hs⟩
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
        exact ih k b rfl _ hs hok
      | halt _ hn _ =>
        rw [hh] at hn
        cases hn

/-- A chain of steps from frames monotone in gas, from `low` with `k` more gas to a stopped `z`.

When the loop runs `low` to a frame `s` with no error, `z` is `s` with `k` more gas. -/
theorem low_of_reaches {hi z : Evm fork Nat} (hr : Reaches (StepG fork) hi z)
    (hz : z.running = false) :
    ∀ (k : Nat) (low : Evm fork Nat), hi = addGas k low →
      ∀ (within : GasMeter.gasHeld low.gas ≤ bound) {s : Evm fork Nat},
        runFrame (step fork) (step_decreases fork) bound runChild low within = .ok s →
        s.error = none → z = addGas k s := by
  intro k low e within s hs hok
  obtain ⟨m, _, rfl, hm⟩ := reaches_low hr k low e within hs hok
  rw [runFrame_of_running_eq_false (by simpa using hz)] at hm
  cases hm
  rfl

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

Every frame that the loop runs `l` to then has an error. -/
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

/-- A chain of steps from frames monotone in gas, from `low` with `k` more gas to a stuck frame.

Every frame that the loop runs `low` to has an error. -/
theorem not_ok_of_reaches {hi z : Evm fork Nat} (hr : Reaches (StepG fork) hi z) (hz : Stuck z) :
    ∀ (k : Nat) (low : Evm fork Nat), hi = addGas k low →
      ∀ (within : GasMeter.gasHeld low.gas ≤ bound) {s : Evm fork Nat},
        runFrame (step fork) (step_decreases fork) bound runChild low within = .ok s →
        s.error ≠ none := by
  intro k low e within s hs hok
  obtain ⟨m, _, rfl, hm⟩ := reaches_low hr k low e within hs hok
  exact error_ne_none_of_stepFails (by simpa using hz.1) (hz.2 k m rfl) hm hok

/-- A frame that, with any gas from `B` on, reaches a stuck frame by steps monotone in gas.

Every frame that the loop runs it to, with any gas, has an error. -/
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

Every frame that the loop runs it to has an error. -/
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
