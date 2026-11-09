module

public import EthLib.Execution.Proofs.Evm.Logic.FailsOn
public import EthLib.Execution.Proofs.Evm.Logic.LessGas

/-!
# Proofs: the runs that succeed

A run succeeds when the loop of the interpreter ends its frame in a frame with no error.

A specification to frames with no error gives a run that succeeds.

So does a specification whose run may stop only when the runner fails.

The runner must then never fail on the messages that the specification names.

A condition that gives such a specification holds exactly when the run succeeds.

The run must meet that condition whenever it succeeds.

The rest is for the meter of one counter of gas, the meter of every fork before Glamsterdam.

Take a specification over steps monotone in gas, to a normal halt that pays `cost`.

Say it holds from a frame with every gas from some bound on, and that bound is at least `cost`.

Every run from that frame with any gas that succeeds then had at least `cost` gas.

It ends in that halt, with exactly `cost` less gas.

So no run with less gas than `cost` succeeds.

Take a specification over such steps to frames with an error, with every gas from some bound on.

Then no run from that frame succeeds, with any gas.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)

variable {fork : Fork}

/-! ## A run that succeeds -/

section Meter

variable {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter] {bound : Nat}
  {runChild : MessageRunner fork Meter bound}
  {evm : Evm fork Meter}

/-- Whether the loop of the interpreter ends the frame `evm` in a frame with no error.

The loop runs with the bound `bound` on the gas of messages and the runner `runChild`. -/
def RunsOk (bound : Nat) (runChild : MessageRunner fork Meter bound) (evm : Evm fork Meter)
    (within : GasMeter.gasHeld evm.gas ≤ bound) : Prop :=
  ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok stopped ∧
    stopped.error = none

/-- A specification to frames with no error gives a run that succeeds, from its precondition.

It holds for every bound on the gas of messages and every runner of messages. -/
theorem Spec.runsOk {P Q : Evm fork Meter → Prop} (h : Spec fork P Q)
    (hQ : ∀ stopped, Q stopped → stopped.error = none) (hp : P evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) : RunsOk bound runChild evm within :=
  let ⟨stopped, hs, hq⟩ := Spec.runFrame h hp within (runChild := runChild)
  ⟨stopped, hs, hQ stopped hq⟩

/-- A specification to frames with no error, whose run may stop only when the runner fails.

It gives a run that succeeds, from its precondition.

The frames of the runner must meet the assumption of the specification.

The runner must never fail on a message of `S`. -/
theorem SpecOn.runsOk {callee : Evm fork Meter → Message fork → Evm fork Meter → Prop}
    {S : Evm fork Meter → Message fork → Prop} {P Q : Evm fork Meter → Prop}
    (h : SpecOn fork callee S P Q) (meets : MeetsOk callee runChild)
    (never : ∀ caller message lt e, S caller message → runChild caller message lt ≠ .error e)
    (hQ : ∀ stopped, Q stopped → stopped.error = none) (hp : P evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) : RunsOk bound runChild evm within := by
  rcases SpecOn.runFrame h meets hp within with ⟨stopped, hs, hq⟩ |
    ⟨-, caller, message, -, lt, e, -, -, -, hS, failed, -⟩
  · exact ⟨stopped, hs, hQ stopped hq⟩
  · exact absurd failed (never caller message lt e hS)

/-- A condition `G` holds exactly when the run succeeds.

Under `G`, a specification to frames with no error must hold from a frame of its precondition.

Every run that succeeds must meet `G`. -/
theorem runsOk_iff {G : Prop} {P Q : Evm fork Meter → Prop} (hspec : G → Spec fork P Q)
    (hQ : ∀ stopped, Q stopped → stopped.error = none) (hp : P evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) (hcomp : RunsOk bound runChild evm within → G) :
    RunsOk bound runChild evm within ↔ G :=
  ⟨hcomp, fun hG => (hspec hG).runsOk hQ hp within⟩

end Meter

/-! ## The gas of a run that succeeds -/

section Gas

variable {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}
  {returnData : ByteArray} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm stopped : Evm fork Nat}

/-- A specification to a normal halt that pays `cost`, from a frame with every gas from `B` on.

Here `B` is at least `cost`.

Say the loop runs that frame with any gas to a frame `stopped` with no error.

That frame then had at least `cost` gas.

Then `stopped` is that halt, with exactly `cost` less gas. -/
theorem halted_of_specG {B cost : Nat} (hcost : cost ≤ B) {output : ByteArray}
    {state' : State.TransactionState} {substate' : Substate}
    (h : ∀ g, B ≤ g → SpecG fork (At code message pc stack memory g state substate returnData)
      (Halted false output (g - cost) state' substate'))
    (start : At code message pc stack memory gas state substate returnData evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hs : runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok stopped)
    (hok : stopped.error = none) :
    cost ≤ gas ∧ stopped.running = false ∧ stopped.output = output ∧
      stopped.gas = gas - cost ∧ stopped.state = state' ∧ stopped.substate = substate' := by
  obtain ⟨hr, ho, hg, hst, hss⟩ :=
    SpecG.halted (h (gas + B) (Nat.le_add_left B gas)) start within hs hok
  exact ⟨by omega, hr, ho, by omega, hst, hss⟩

/-- A specification to frames with an error, from a frame with every gas from `B` on.

When the loop runs that frame with any gas, it ends in a frame with an error. -/
theorem no_ok_of_specG {B : Nat} {Q : Nat → Evm fork Nat → Prop}
    (h : ∀ g, B ≤ g →
      SpecG fork (At code message pc stack memory g state substate returnData) (Q g))
    (herr : ∀ g evm, Q g evm → evm.error ≠ none)
    (start : At code message pc stack memory gas state substate returnData evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hs : runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok stopped) :
    stopped.error ≠ none :=
  SpecG.not_ok (h (gas + B) (Nat.le_add_left B gas)) (herr (gas + B)) (start.addGas B) within hs

/-- No run with less gas than `cost` succeeds.

Every run that succeeds must meet a condition `G`.

Under `G`, a specification to a normal halt that pays `cost` must hold from the frame.

It must hold with every gas from `B` on.

Here `B` is at least `cost`. -/
theorem not_runsOk_of_lt {G : Prop} {B cost : Nat} (hcost : cost ≤ B) (hlt : gas < cost)
    {output : ByteArray} {state' : State.TransactionState} {substate' : Substate}
    (hspec : G → ∀ g, B ≤ g →
      SpecG fork (At code message pc stack memory g state substate returnData)
        (Halted false output (g - cost) state' substate'))
    (start : At code message pc stack memory gas state substate returnData evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) (hcomp : RunsOk bound runChild evm within → G) :
    ¬RunsOk bound runChild evm within := by
  intro hok
  obtain ⟨stopped, hs, herr⟩ := hok
  have := (halted_of_specG hcost (hspec (hcomp ⟨stopped, hs, herr⟩)) start within hs herr).1
  omega

/-- No run succeeds when under a condition `G` the frame reaches a stuck frame with its own gas.

Every run that succeeds must meet `G`. -/
theorem not_runsOk_of_stuck {G : Prop}
    (hstuck : G →
      HoareG fork (At code message pc stack memory gas state substate returnData) Stuck)
    (start : At code message pc stack memory gas state substate returnData evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) (hcomp : RunsOk bound runChild evm within → G) :
    ¬RunsOk bound runChild evm within := by
  intro hok
  obtain ⟨stopped, hs, herr⟩ := hok
  exact no_ok_stuck_at (hstuck (hcomp ⟨stopped, hs, herr⟩)) start within hs herr

end Gas

/-! ## An exact threshold of gas -/

/-- The form of an exact threshold of gas, at the larger of `first` and `second`.

Say `R` holds exactly when `G` does, with at least `first` and at least `second` gas.

Say `R` fails below `first`, and from `first` to below `second`.

Then `R` holds exactly when `G` holds and the gas is at least the larger of `first` and `second`.
-/
theorem iff_and_max_le {R G : Prop} {first second gas : Nat}
    (hok : first ≤ gas → second ≤ gas → (R ↔ G)) (hlow : gas < first → ¬R)
    (hmid : first ≤ gas → gas < second → ¬R) : R ↔ G ∧ max first second ≤ gas := by
  constructor
  · intro h
    have hfirst : first ≤ gas := Nat.le_of_not_lt fun hl => hlow hl h
    have hsecond : second ≤ gas := Nat.le_of_not_lt fun hl => hmid hfirst hl h
    exact ⟨(hok hfirst hsecond).1 h, Nat.max_le.mpr ⟨hfirst, hsecond⟩⟩
  · rintro ⟨hG, hmax⟩
    exact (hok (Nat.max_le.mp hmax).1 (Nat.max_le.mp hmax).2).2 hG

end EthLib.Execution.Evm.Logic
