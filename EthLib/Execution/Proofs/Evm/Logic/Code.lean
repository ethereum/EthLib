module

public import EthLib.Execution.Proofs.Evm.CodeKept
public import EthLib.Execution.Proofs.Evm.Logic.Message

/-!
# Proofs: every frame of a run has the jump destinations of its code

Each step keeps the code and its destinations, under every runner of messages.

A message starts with the destinations of its code, so every frame that a run reaches has them.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

variable [LawfulGasMeter Meter]

/-- A step keeps the code and its valid jump destinations. -/
theorem Step.keepsCode {evm after : Evm fork Meter} (h : Step fork evm after) :
    after.code = evm.code ∧ after.validJumpDestinations = evm.validJumpDestinations := by
  cases h with
  | next _ hs => exact step_keepsCode hs
  | halt => exact ⟨rfl, rfl⟩

/-- A step under a runner of messages keeps the code and its valid jump destinations. -/
theorem StepBy.keepsCode {bound : Nat} {runChild : MessageRunner fork Meter bound}
    {evm after : Evm fork Meter} (h : StepBy fork bound runChild evm after) :
    after.code = evm.code ∧ after.validJumpDestinations = evm.validJumpDestinations := by
  cases h with
  | step hs => exact hs.keepsCode
  | child _ hs _ _ hr => exact ((step_keepsCode hs).2.2 _ _ hr)
  | childHalt => exact ⟨rfl, rfl⟩

omit [GasMeter Meter] [LawfulGasMeter Meter] in
/-- Every frame that a run reaches has the code and the destinations of its first frame.

Each step of the run must keep them. -/
theorem Reaches.keepsCode {S : Evm fork Meter → Evm fork Meter → Prop}
    (keeps : ∀ {a b}, S a b →
      b.code = a.code ∧ b.validJumpDestinations = a.validJumpDestinations)
    {evm after : Evm fork Meter} (h : Reaches S evm after) :
    after.code = evm.code ∧ after.validJumpDestinations = evm.validJumpDestinations :=
  h.invariant (R := fun b => b.code = evm.code ∧
      b.validJumpDestinations = evm.validJumpDestinations)
    (fun hs ⟨code, jumps⟩ => ⟨(keeps hs).1.trans code, (keeps hs).2.trans jumps⟩) ⟨rfl, rfl⟩

omit [GasMeter Meter] [LawfulGasMeter Meter] in
/-- Every frame that a run reaches from a frame with its destinations has them.

Each step of the run must keep the code and the destinations. -/
theorem Reaches.hasDestinations {S : Evm fork Meter → Evm fork Meter → Prop}
    (keeps : ∀ {a b}, S a b →
      b.code = a.code ∧ b.validJumpDestinations = a.validJumpDestinations)
    {evm after : Evm fork Meter} (h : Reaches S evm after) (start : HasDestinations evm) :
    HasDestinations after := by
  obtain ⟨code, jumps⟩ := h.keepsCode keeps
  unfold HasDestinations at start ⊢
  rw [code, jumps, start]

/-- Every frame that a run of a message reaches has the jump destinations of its code.

The steps send no message, or a runner of messages ends each one. -/
theorem Reaches.hasDestinations_startFrame {bound : Nat}
    {runChild : MessageRunner fork Meter bound} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {meter : Meter} {after : Evm fork Meter}
    (h : Reaches (StepBy fork bound runChild) (startFrame message state substate meter) after) :
    HasDestinations after :=
  h.hasDestinations StepBy.keepsCode (Evm.hasDestinations_startFrame message state substate meter)

end EthLib.Execution.Evm.Logic
