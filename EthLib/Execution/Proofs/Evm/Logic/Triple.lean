module

public import EthLib.Execution.Proofs.Evm.Logic.Reach

/-!
# Proofs: triples over the frames of the EVM

A triple says that from every frame of its precondition, the steps reach one of its postcondition.

The rules of triples hold for every relation of steps, so the steps with messages share them.

A triple over the steps without a message is total correctness: the reached frame exists.

No gas bound is needed for the run to end, since every run of the loop ends by its measure.

But a run can end in an exceptional halt, such as out of gas.

So a postcondition that asks for a normal halt needs a precondition with enough gas.

A specification asks for a stopped frame, the end of the run.

The steps are deterministic, so that frame is the one result of the loop of the interpreter.

The rules compose triples in sequence, weaken them, and carry an invariant of every step along.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork)

variable {fork : Fork} {Meter : Type}

/-- From every frame that `P` holds of, the steps of `S` reach a frame that `Q` holds of. -/
def Triple (S : Evm fork Meter → Evm fork Meter → Prop) (P Q : Evm fork Meter → Prop) : Prop :=
  ∀ evm, P evm → ∃ after, Reaches S evm after ∧ Q after

namespace Triple

variable {S : Evm fork Meter → Evm fork Meter → Prop}

/-- A precondition that implies the postcondition needs no step. -/
theorem of_imp {P Q : Evm fork Meter → Prop} (h : ∀ evm, P evm → Q evm) : Triple S P Q :=
  fun evm hp => ⟨evm, .refl evm, h evm hp⟩

/-- One step from each frame of the precondition to a frame of the postcondition. -/
theorem of_step {P Q : Evm fork Meter → Prop}
    (h : ∀ evm, P evm → ∃ after, S evm after ∧ Q after) : Triple S P Q :=
  fun evm hp =>
    let ⟨after, hs, hq⟩ := h evm hp
    ⟨after, .single hs, hq⟩

/-- Sequence: reach the middle condition, then the postcondition from it. -/
theorem seq {P Q R : Evm fork Meter → Prop} (first : Triple S P Q) (second : Triple S Q R) :
    Triple S P R := fun evm hp =>
  let ⟨mid, h₁, hq⟩ := first evm hp
  let ⟨after, h₂, hr⟩ := second mid hq
  ⟨after, h₁.trans h₂, hr⟩

/-- Consequence: a stronger precondition and a weaker postcondition. -/
theorem consequence {P P' Q Q' : Evm fork Meter → Prop} (h : Triple S P Q)
    (pre : ∀ evm, P' evm → P evm) (post : ∀ evm, Q evm → Q' evm) : Triple S P' Q' :=
  fun evm hp =>
    let ⟨after, hr, hq⟩ := h evm (pre evm hp)
    ⟨after, hr, post after hq⟩

/-- Invariant: a predicate that every step keeps holds at both ends of a triple. -/
theorem invariant {P Q R : Evm fork Meter → Prop} (h : Triple S P Q)
    (keeps : ∀ {a b}, S a b → R a → R b) :
    Triple S (fun evm => P evm ∧ R evm) (fun evm => Q evm ∧ R evm) :=
  fun evm ⟨hp, hr⟩ =>
    let ⟨after, hreach, hq⟩ := h evm hp
    ⟨after, hreach, hq, hreach.invariant (S := S) keeps hr⟩

/-- Each case of the precondition with its own triple. -/
theorem cases {P₁ P₂ Q : Evm fork Meter → Prop} (h₁ : Triple S P₁ Q) (h₂ : Triple S P₂ Q) :
    Triple S (fun evm => P₁ evm ∨ P₂ evm) Q :=
  fun evm hp => hp.elim (h₁ evm) (h₂ evm)

end Triple

variable [GasMeter Meter]

/-- From every frame that `P` holds of, the frame reaches a frame that `Q` holds of. -/
abbrev Hoare (fork : Fork) (P Q : Evm fork Meter → Prop) : Prop :=
  Triple (Step fork) P Q

/-- From every frame that `P` holds of, the frame reaches a stopped frame that `Q` holds of. -/
def Spec (fork : Fork) (P Q : Evm fork Meter → Prop) : Prop :=
  Hoare fork P fun evm => evm.running = false ∧ Q evm

namespace Spec

/-- A triple to a frame from which the specification holds. -/
theorem seq {P Q R : Evm fork Meter → Prop} (first : Hoare fork P Q) (second : Spec fork Q R) :
    Spec fork P R := Triple.seq first second

/-- Consequence for a specification. -/
theorem consequence {P P' Q Q' : Evm fork Meter → Prop} (h : Spec fork P Q)
    (pre : ∀ evm, P' evm → P evm) (post : ∀ evm, Q evm → Q' evm) : Spec fork P' Q' :=
  Triple.consequence h pre fun evm ⟨hs, hq⟩ => ⟨hs, post evm hq⟩

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
