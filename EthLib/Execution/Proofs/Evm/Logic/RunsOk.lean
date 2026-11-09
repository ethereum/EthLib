module

public import EthLib.Execution.Proofs.Evm.Logic.FailsOn
public import EthLib.Execution.Proofs.Evm.Logic.LessGas

/-!
# Proofs: the runs that succeed

A run succeeds when the loop of the interpreter ends its frame in a frame with no error.

A frame that reverts has an error, so its run does not succeed.

A specification to frames with no error gives a run that succeeds.

So does a specification whose runner may fail only on the messages that it names.

The runner must then never fail on those messages.

For the meter of one counter of gas, no run with less gas than a halt pays succeeds.

That holds when a specification to that halt holds with any gas from some bound on.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)

variable {fork : Fork}

/-! ## A run that succeeds -/

/-- Whether the loop of the interpreter ends the frame `evm` in a frame with no error.

The loop bounds the gas of messages by `bound` and runs them with `runChild`.

A frame that reverts has an error, so its run does not succeed. -/
def RunsOk {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter] (bound : Nat)
    (runChild : MessageRunner fork Meter bound) (evm : Evm fork Meter)
    (within : GasMeter.gasHeld evm.gas ≤ bound) : Prop :=
  ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok stopped ∧
    stopped.error = none

section Meter

variable {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter] {bound : Nat}
  {runChild : MessageRunner fork Meter bound}
  {evm : Evm fork Meter}

/-- A specification to frames with no error gives a run that succeeds, from its precondition.

It holds for every bound on the gas of messages and every runner of messages. -/
theorem Spec.runsOk {P Q : Evm fork Meter → Prop} (h : Spec fork P Q)
    (hQ : ∀ stopped, Q stopped → stopped.error = none) (hp : P evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) : RunsOk bound runChild evm within :=
  let ⟨stopped, hs, hq⟩ := Spec.runFrame h hp within (runChild := runChild)
  ⟨stopped, hs, hQ stopped hq⟩

/-- A specification to frames with no error, whose runner may fail on the messages of `S`.

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

end Meter

/-! ## The gas of a run that succeeds -/

section Gas

variable {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}
  {returnData : ByteArray} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm : Evm fork Nat}

/-- No run with less gas than `cost` succeeds.

A specification to a normal halt that pays `cost` must hold from the frame.

It must hold with any gas from `B` on that is at least `cost`. -/
theorem not_runsOk_of_lt {B cost : Nat} (hlt : gas < cost) {output : ByteArray}
    {state' : State.TransactionState} {substate' : Substate}
    (hspec : ∀ g, B ≤ g → cost ≤ g →
      SpecG fork (At code message pc stack memory g state substate returnData)
        (Halted false output (g - cost) state' substate'))
    (start : At code message pc stack memory gas state substate returnData evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) : ¬RunsOk bound runChild evm within := by
  rintro ⟨stopped, hs, herr⟩
  have := (halted_of_specG hspec start within hs herr).1
  omega

end Gas

end EthLib.Execution.Evm.Logic
