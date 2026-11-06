module

public import EthLib.Execution.Proofs.Evm.Logic.Reach

/-!
# Proofs: triples over the frames of the EVM

A triple `Hoare fork P Q` says: from every frame of `P`, the steps reach a frame of `Q`.

It is total correctness for the frames that send no message: the reached frame exists.

No gas bound is needed for the run to end, since every run of the loop ends by its measure.

But a run can end in an exceptional halt, such as out of gas.

So a postcondition that asks for a normal halt needs a precondition with enough gas.

`Spec fork P Q` asks for a stopped frame, the end of the run.

The steps are deterministic, so that frame is the one result of the run, which `runFrame` gives.

The rules compose triples in sequence, weaken them, and carry an invariant of every step along.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- From every frame that `P` holds of, the frame reaches a frame that `Q` holds of. -/
def Hoare (fork : Fork) (P Q : Evm fork Meter → Prop) : Prop :=
  ∀ evm, P evm → ∃ after, Reaches fork evm after ∧ Q after

/-- From every frame that `P` holds of, the frame reaches a stopped frame that `Q` holds of. -/
def Spec (fork : Fork) (P Q : Evm fork Meter → Prop) : Prop :=
  Hoare fork P fun evm => evm.running = false ∧ Q evm

namespace Hoare

/-- A precondition that implies the postcondition needs no step. -/
theorem of_imp {P Q : Evm fork Meter → Prop} (h : ∀ evm, P evm → Q evm) : Hoare fork P Q :=
  fun evm hp => ⟨evm, .refl evm, h evm hp⟩

/-- One step from each frame of the precondition to a frame of the postcondition. -/
theorem of_step {P Q : Evm fork Meter → Prop}
    (h : ∀ evm, P evm → ∃ after, Step fork evm after ∧ Q after) : Hoare fork P Q :=
  fun evm hp =>
    let ⟨after, hs, hq⟩ := h evm hp
    ⟨after, .single hs, hq⟩

/-- Sequence: reach the middle condition, then the postcondition from it. -/
theorem seq {P Q R : Evm fork Meter → Prop} (first : Hoare fork P Q) (second : Hoare fork Q R) :
    Hoare fork P R := fun evm hp =>
  let ⟨mid, h₁, hq⟩ := first evm hp
  let ⟨after, h₂, hr⟩ := second mid hq
  ⟨after, h₁.trans h₂, hr⟩

/-- Consequence: a stronger precondition and a weaker postcondition. -/
theorem consequence {P P' Q Q' : Evm fork Meter → Prop} (h : Hoare fork P Q)
    (pre : ∀ evm, P' evm → P evm) (post : ∀ evm, Q evm → Q' evm) : Hoare fork P' Q' :=
  fun evm hp =>
    let ⟨after, hr, hq⟩ := h evm (pre evm hp)
    ⟨after, hr, post after hq⟩

/-- Frame: a predicate that every step keeps holds at both ends of a triple. -/
theorem frame {P Q R : Evm fork Meter → Prop} (h : Hoare fork P Q)
    (keeps : ∀ {a b}, Step fork a b → R a → R b) :
    Hoare fork (fun evm => P evm ∧ R evm) (fun evm => Q evm ∧ R evm) :=
  fun evm ⟨hp, hr⟩ =>
    let ⟨after, hreach, hq⟩ := h evm hp
    ⟨after, hreach, hq, hreach.invariant keeps hr⟩

/-- Each case of the precondition with its own triple. -/
theorem cases {P₁ P₂ Q : Evm fork Meter → Prop} (h₁ : Hoare fork P₁ Q)
    (h₂ : Hoare fork P₂ Q) :
    Hoare fork (fun evm => P₁ evm ∨ P₂ evm) Q :=
  fun evm hp => hp.elim (h₁ evm) (h₂ evm)

end Hoare

namespace Spec

/-- A specification is a triple that ends in a stopped frame. -/
theorem of_hoare {P Q : Evm fork Meter → Prop}
    (h : Hoare fork P fun evm => evm.running = false ∧ Q evm) : Spec fork P Q := h

/-- A triple to a frame from which the specification holds. -/
theorem seq {P Q R : Evm fork Meter → Prop} (first : Hoare fork P Q) (second : Spec fork Q R) :
    Spec fork P R := Hoare.seq first second

/-- Consequence for a specification. -/
theorem consequence {P P' Q Q' : Evm fork Meter → Prop} (h : Spec fork P Q)
    (pre : ∀ evm, P' evm → P evm) (post : ∀ evm, Q evm → Q' evm) : Spec fork P' Q' :=
  Hoare.consequence h pre fun evm ⟨hs, hq⟩ => ⟨hs, post evm hq⟩

/-- From a frame of the precondition, the loop of the interpreter gives one of the postcondition.

It holds for every bound on the gas of messages and every runner of messages. -/
theorem runFrame [LawfulGasMeter Meter] {P Q : Evm fork Meter → Prop} (h : Spec fork P Q)
    {bound : Nat} {runChild : MessageRunner fork Meter bound} {evm : Evm fork Meter}
    (hp : P evm) (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ Q stopped :=
  let ⟨stopped, hreach, halted, hq⟩ := h evm hp
  ⟨stopped, runFrame_of_reaches hreach halted within, hq⟩

end Spec

end EthLib.Execution.Evm.Logic
