module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Proofs.Evm.Call.MessageCall

/-!
# Proofs: a property of each step holds for a whole run of a message

A property of a run is a relation between two frames of the same message.

It must be reflexive and transitive.

A step that sends a message relates its frame to the caller frame and to the frame that resumes.

The frame that resumes needs a fact about the frame that ends the message.

That fact relates the message, its start state, substate and meter, and the frame that ends it.

When each step keeps the relation, so does a whole run of a frame.

This needs a runner of messages that gives the fact.

The fact then holds of every call and creation, by strong induction on the gas of the message.

Each property supplies its steps, its halts, the start of a call, its rollback and its deposit of
code.

The steps may assume a frame invariant that the relation keeps.

The run then needs that invariant at its start.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## A step -/

/-- What a step from `evm` gives, for a relation `R` of frames and a relation `C` of messages.

The next frame is related to `evm`.

A message is sent from a frame related to `evm`.

The frame that resumes is related to `evm` too.

This needs `C` to hold of the caller, the message and the frame that ends the message. -/
def StepResult.Keeps (R : Evm fork Meter → Evm fork Meter → Prop)
    (C : Evm fork Meter → Message fork → Evm fork Meter → Prop) (evm : Evm fork Meter) :
    StepResult fork Meter → Prop
  | .next after => R evm after
  | .child caller message resume => R evm caller ∧
      ∀ child after, resume child = .ok after → C caller message child → R evm after

omit [GasMeter Meter] in
/-- A result related to a frame is related to each frame before it. -/
theorem StepResult.Keeps.lift {R : Evm fork Meter → Evm fork Meter → Prop}
    {C : Evm fork Meter → Message fork → Evm fork Meter → Prop}
    (trans : ∀ {a b c}, R a b → R b c → R a c) {evm evm' : Evm fork Meter}
    {result : StepResult fork Meter} (h : R evm evm') (r : StepResult.Keeps R C evm' result) :
    StepResult.Keeps R C evm result := by
  cases result with
  | next after => exact trans h r
  | child caller message resume =>
    obtain ⟨c, m⟩ := r
    exact ⟨trans h c, fun child after hres p => trans h (m child after hres p)⟩

omit [GasMeter Meter] in
/-- Two relations that a step keeps, it keeps together. -/
theorem StepResult.Keeps.and {R S : Evm fork Meter → Evm fork Meter → Prop}
    {C D : Evm fork Meter → Message fork → Evm fork Meter → Prop} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (r : StepResult.Keeps R C evm result)
    (s : StepResult.Keeps S D evm result) :
    StepResult.Keeps (fun a b => R a b ∧ S a b) (fun a m b => C a m b ∧ D a m b) evm result := by
  cases result with
  | next after => exact ⟨r, s⟩
  | child caller message resume =>
    obtain ⟨rc, rm⟩ := r
    obtain ⟨sc, sm⟩ := s
    exact ⟨⟨rc, sc⟩, fun child after hres p => ⟨rm child after hres p.1, sm child after hres p.2⟩⟩

/-! ## A run of a frame -/

section Frame

variable {R : Evm fork Meter → Evm fork Meter → Prop}
  {C : Evm fork Meter → Message fork → Evm fork Meter → Prop} {Inv : Evm fork Meter → Prop}
  {step : Evm fork Meter → Except EvmError (StepResult fork Meter)}
  {decreases : ∀ {evm result}, evm.running = true → step evm = .ok result →
    result.Decreases evm}
  {bound : Nat} {runChild : MessageRunner fork Meter bound}

/-- A successful run of a frame is related to the frame it starts from.

The relation must be reflexive and transitive, and hold of each exceptional halt.

Each step from a frame with the invariant must keep the relation, which keeps the invariant.

The runner must end each message from a caller with the invariant in a frame that `C` relates.

The run must start from a frame with the invariant. -/
theorem rel_runFrame (refl : ∀ evm, R evm evm) (trans : ∀ {a b c}, R a b → R b c → R a c)
    (keeps : ∀ {a b}, Inv a → R a b → Inv b)
    (halt : ∀ evm error, Inv evm → R evm (exceptionalHalt evm error))
    (steps : ∀ {evm result}, Inv evm → step evm = .ok result → StepResult.Keeps R C evm result)
    (runs : ∀ caller message lt ended, Inv caller → runChild caller message lt = .ok ended →
      C caller message ended.val)
    {evm after : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound} (start : Inv evm)
    (h : runFrame step decreases bound runChild evm within = .ok after) : R evm after := by
  fun_induction runFrame step decreases bound runChild evm within
  case case1 => cases h
  case case2 => cases h; exact halt _ _ start
  case case3 =>
    rename_i result _ ih
    have r : R _ _ := steps start result
    exact trans r (ih (keeps start r) h)
  case case4 => cases h
  case case5 => cases h
  case case6 => cases h; exact halt _ _ start
  case case7 =>
    rename_i hchild _ _ _ hran _ resumed _ ih
    obtain ⟨c, hres⟩ := steps start hchild
    have r := hres _ _ resumed (runs _ _ _ _ (keeps start c) hran)
    exact trans r (ih (keeps start r) h)
  case case8 => cases h; exact refl _

end Frame

/-! ## Messages -/

/-- A relation `M` of messages, as a relation of a caller, a message and the frame that ends it.

The message starts from the caller's state, a child of the caller's substate and a new meter. -/
def ChildRel
    (M : Message fork → TransactionState → Substate → Meter → Evm fork Meter → Prop)
    (caller : Evm fork Meter) (message : Message fork) (ended : Evm fork Meter) : Prop :=
  M message caller.state caller.substate.child (GasMeter.start message.gas message.reservoir)
    ended

/-- Every successful call and creation satisfies a relation `M` of messages, at every fork.

The relation `R` of frames must be reflexive and transitive, and keep the invariant `Inv`.

It must hold of each exceptional halt, each stop and each precompile, from a frame with the
invariant.

Each step from a frame with the invariant must keep `R`, given `M` for the messages it sends.

A call must satisfy `M` after its rollback, when its frame ends related to the frame it starts
from.

That frame starts from the state and substate before or after the transfer of value.

A call may use that relation only when its start frame has the invariant.

A creation must satisfy `M` when the call of its init code does, after its deposit of code.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
theorem processMessage_rel [LawfulGasMeter Meter]
    {R : Evm fork Meter → Evm fork Meter → Prop} {Inv : Evm fork Meter → Prop}
    {M : Message fork → TransactionState → Substate → Meter → Evm fork Meter → Prop}
    (refl : ∀ evm, R evm evm) (trans : ∀ {a b c}, R a b → R b c → R a c)
    (keeps : ∀ {a b}, Inv a → R a b → Inv b)
    (halt : ∀ evm error, Inv evm → R evm (exceptionalHalt evm error))
    (steps : ∀ {evm result}, Inv evm → step fork evm = .ok result →
      StepResult.Keeps R (ChildRel M) evm result)
    (stop : ∀ evm : Evm fork Meter, Inv evm → R evm { evm with running := false })
    (precompile : ∀ {address : Nat} {evm after : Evm fork Meter},
      runPrecompile fork address evm = some after → Inv evm → R evm after)
    (call : ∀ {message : Message fork} {state state1 : TransactionState}
      {substate substate1 : Substate} {meter : Meter} {ended : Evm fork Meter},
      (state1 = startState fork message state ∧ substate1 = substate ∧
          ¬(message.shouldTransferValue = true ∧ message.value ≠ 0) ∨
        (message.shouldTransferValue = true ∧ message.value ≠ 0) ∧
          (startState fork message state).moveEther fork message.caller message.currentTarget
            message.value = .ok state1 ∧
          substate1 = { substate with
            logs := pushTransferLog fork substate.logs message.caller message.currentTarget
              message.value }) →
      (Inv (startFrame message state1 substate1 meter) →
        R (startFrame message state1 substate1 meter) ended) →
      M message state substate meter (rollbackOnError state ended))
    (create : ∀ {message : Message fork} {state prepared : TransactionState}
      {substate : Substate} {meter : Meter} {evm after : Evm fork Meter},
      prepareCreation fork state message.currentTarget = .ok prepared →
      M message prepared substate meter evm → depositCode fork state evm = .ok after →
      M message state substate meter after)
    (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        M message state substate meter ended.val) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        M message state substate meter ended.val) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    have callCase : ∀ (message : Message fork) (state : TransactionState) (substate : Substate)
        (meter : Meter) (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
        ∀ ended, processMessage fork message state substate meter held = .ok ended →
          M message state substate meter ended.val := by
      intro message state substate meter held hn ended h
      rw [processMessage] at h
      obtain ⟨ended0, hdo, rolled⟩ := Base.map_ok_iff.mp h
      have hval := congrArg Subtype.val rolled
      simp only at hval
      rw [← hval]
      dsimp only at hdo
      split at hdo
      all_goals obtain ⟨state1, hm, hdo⟩ := Base.bind_ok_iff.mp hdo
      all_goals
        rcases hpa : precompileAddress fork message with _ | addr
        · simp only [hpa] at hdo
          split at hdo
          · cases hdo
          · rename_i after hrun
            cases hdo
            refine call (by first
                | exact Or.inr ⟨‹message.shouldTransferValue = true ∧ message.value ≠ 0›,
                    Base.mapError_ok_iff.mp hm,
                    by first | rfl | (split <;> first | rfl | contradiction)⟩
                | (cases hm
                   exact Or.inl ⟨rfl, by first | rfl | (split <;> first | rfl | contradiction),
                     ‹_›⟩))
              fun hinv => rel_runFrame refl trans keeps halt steps ?_ hinv hrun
            rintro caller' message' lt ⟨c, used⟩ - hrun'
            split at hrun'
            · exact (ih message'.gas (by omega)).1 message' caller'.state _ _ _ rfl ⟨c, used⟩
                hrun'
            · exact (ih message'.gas (by omega)).2 message' caller'.state _ _ _ rfl ⟨c, used⟩
                hrun'
        · simp only [hpa] at hdo
          split at hdo
          · cases hdo
            exact call (by first
                | exact Or.inr ⟨‹message.shouldTransferValue = true ∧ message.value ≠ 0›,
                    Base.mapError_ok_iff.mp hm,
                    by first | rfl | (split <;> first | rfl | contradiction)⟩
                | (cases hm
                   exact Or.inl ⟨rfl, by first | rfl | (split <;> first | rfl | contradiction),
                     ‹_›⟩)) (stop _)
          · split at hdo
            · rename_i after hrp
              cases hdo
              exact call (by first
                | exact Or.inr ⟨‹message.shouldTransferValue = true ∧ message.value ≠ 0›,
                    Base.mapError_ok_iff.mp hm,
                    by first | rfl | (split <;> first | rfl | contradiction)⟩
                | (cases hm
                   exact Or.inl ⟨rfl, by first | rfl | (split <;> first | rfl | contradiction),
                     ‹_›⟩)) (precompile hrp)
            · cases hdo
              exact call (by first
                | exact Or.inr ⟨‹message.shouldTransferValue = true ∧ message.value ≠ 0›,
                    Base.mapError_ok_iff.mp hm,
                    by first | rfl | (split <;> first | rfl | contradiction)⟩
                | (cases hm
                   exact Or.inl ⟨rfl, by first | rfl | (split <;> first | rfl | contradiction),
                     ‹_›⟩)) (stop _)
    refine ⟨callCase, ?_⟩
    intro message state substate meter held hn ended h
    rw [processCreateMessage] at h
    obtain ⟨prepared, hp, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨evm, used⟩, hrun, h⟩ := Base.bind_ok_iff.mp h
    dsimp only at h
    split at h
    · cases h
    · cases h
      exact create hp (callCase message prepared substate meter held hn _ hrun)
        ‹depositCode _ _ _ = .ok _›

end EthLib.Execution.Evm
