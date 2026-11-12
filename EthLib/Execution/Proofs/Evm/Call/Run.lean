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

Each property supplies its steps, its halts and the start of a call.

It also supplies the rollback of a call and the deposit of code.

The steps may assume a frame invariant that the relation keeps.

The run then needs that invariant at its start.

A call starts from the state it enters: its target touched before Paris, then its value moved.
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
/-- A result that keeps a relation under a fact of each message keeps it under a stronger fact. -/
theorem StepResult.Keeps.of_child {R : Evm fork Meter → Evm fork Meter → Prop}
    {C D : Evm fork Meter → Message fork → Evm fork Meter → Prop}
    (stronger : ∀ {caller message child}, D caller message child → C caller message child)
    {evm : Evm fork Meter} {result : StepResult fork Meter} (r : StepResult.Keeps R C evm result) :
    StepResult.Keeps R D evm result := by
  cases result with
  | next after => exact r
  | child caller message resume =>
    exact ⟨r.1, fun child after hres p => r.2 child after hres (stronger p)⟩

/-! ## A run of a frame -/

/-- A runner of messages ends each message that it runs successfully in a frame that `C` relates.

`C` relates the frame that sends the message, the message and the frame that ends it. -/
def RunnerEnsures (C : Evm fork Meter → Message fork → Evm fork Meter → Prop) {bound : Nat}
    (runChild : MessageRunner fork Meter bound) : Prop :=
  ∀ caller message lt ended, runChild caller message lt = .ok ended → C caller message ended.val

section Frame

variable {R : Evm fork Meter → Evm fork Meter → Prop}
  {C : Evm fork Meter → Message fork → Evm fork Meter → Prop} {Inv : Evm fork Meter → Prop}
  {step : Evm fork Meter → Except EvmError (StepResult fork Meter)}
  {decreases : ∀ {evm result}, evm.running = true → step evm = .ok result →
    result.Decreases evm}
  {bound : Nat} {runChild : MessageRunner fork Meter bound}

/-- A successful run of a frame is related to the frame it starts from.

The relation must be reflexive and transitive, and hold of each exceptional halt.

Each halt and each step starts from a frame with the invariant.

Each step must keep the relation, which keeps the invariant.

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

/-- The state and the substate that the frame of a message starts from, after those of its caller.

Before Paris, the target of the message is touched first.

A message that moves a value then moves it from its sender to its target.

From Glamsterdam, it also logs a move to another account, by EIP-7708.

Any other message starts from there with the substate of its caller. -/
def Entered (fork : Fork) (message : Message fork) (state : TransactionState)
    (substate : Substate) (entry : TransactionState) (entrySubstate : Substate) : Prop :=
  (¬(message.shouldTransferValue = true ∧ message.value ≠ 0) ∧
      entry = startState fork message state ∧ entrySubstate = substate) ∨
    ((message.shouldTransferValue = true ∧ message.value ≠ 0) ∧
      (startState fork message state).moveEther fork message.caller message.currentTarget
        message.value = .ok entry ∧
      entrySubstate = { substate with
        logs := pushTransferLog fork substate.logs message.caller message.currentTarget
          message.value })

/-- A message that moves no value starts from the start state and the substate of its caller. -/
theorem Entered.of_not_transfers {message : Message fork} {state entry : TransactionState}
    {substate entrySubstate : Substate}
    (h : Entered fork message state substate entry entrySubstate)
    (hno : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0)) :
    entry = startState fork message state ∧ entrySubstate = substate := by
  rcases h with ⟨-, h⟩ | ⟨ht, -⟩
  · exact h
  · exact absurd ht hno

/-- A message enters one state with one substate. -/
theorem Entered.unique {message : Message fork} {state entry entry' : TransactionState}
    {substate entrySubstate entrySubstate' : Substate}
    (h : Entered fork message state substate entry entrySubstate)
    (h' : Entered fork message state substate entry' entrySubstate') :
    entry' = entry ∧ entrySubstate' = entrySubstate := by
  rcases h with ⟨hn, rfl, rfl⟩ | ⟨ht, he, rfl⟩ <;>
    rcases h' with ⟨hn', rfl, rfl⟩ | ⟨ht', he', rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact absurd ht' hn
  · exact absurd ht hn'
  · rw [he] at he'
    exact ⟨(Except.ok.inj he').symm, rfl⟩

/-- A relation `M` of messages, as a relation of a caller, a message and the frame that ends it.

The message starts from the caller's state, a child of the caller's substate and a new meter. -/
def ChildRel
    (M : Message fork → TransactionState → Substate → Meter → Evm fork Meter → Prop)
    (caller : Evm fork Meter) (message : Message fork) (ended : Evm fork Meter) : Prop :=
  M message caller.state caller.substate.child (GasMeter.start message.gas message.reservoir)
    ended

/-- A relation of a caller and a child: by `Mcall` for a call, by `Mcreate` for a creation.

A message with a target is a call, and one with none is a creation. -/
def ChildRelByKind
    (Mcall Mcreate : Message fork → TransactionState → Substate → Meter → Evm fork Meter → Prop)
    (caller : Evm fork Meter) (message : Message fork) (ended : Evm fork Meter) : Prop :=
  match message.target with
  | some _ => ChildRel Mcall caller message ended
  | none => ChildRel Mcreate caller message ended

/-- Every successful call satisfies a relation `Mcall`, and every creation a relation `Mcreate`.

That holds at every fork.

A fact `F` relates the start frame of a call to the frame that ends its code or its precompile.

It must hold of each run of a frame whose message selects no precompile.

That run may use a runner that ends each call by `Mcall` and each creation by `Mcreate`.

It must also hold of each precompile that runs, and of each one skipped, whose frame just stops.

A call must satisfy `Mcall` after its rollback, when `F` relates its start frame to its end.

That frame starts from the state and substate before or after the transfer of value.

After its deposit of code, a creation must satisfy `Mcreate` when its init code satisfies `Mcall`.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
theorem processMessage_frame_byKind [LawfulGasMeter Meter]
    {F : Evm fork Meter → Evm fork Meter → Prop}
    {Mcall Mcreate : Message fork → TransactionState → Substate → Meter → Evm fork Meter → Prop}
    (frame : ∀ {bound : Nat} {runChild : MessageRunner fork Meter bound}
      {evm after : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound},
      RunnerEnsures (ChildRelByKind Mcall Mcreate) runChild →
      precompileAddress fork evm.message = none →
      runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok after →
      F evm after)
    (skip : ∀ {address : Nat} (evm : Evm fork Meter),
      precompileAddress fork evm.message = some address →
      (evm.message.disablePrecompiles = true ∨ runPrecompile fork address evm = none) →
      F evm { evm with running := false })
    (precompile : ∀ {address : Nat} {evm after : Evm fork Meter},
      precompileAddress fork evm.message = some address →
      evm.message.disablePrecompiles = false → runPrecompile fork address evm = some after →
      F evm after)
    (call : ∀ {message : Message fork} {state entry : TransactionState}
      {substate entrySubstate : Substate} {meter : Meter} {ended : Evm fork Meter},
      Entered fork message state substate entry entrySubstate →
      F (startFrame message entry entrySubstate meter) ended →
      Mcall message state substate meter (rollbackOnError state ended))
    (create : ∀ {message : Message fork} {state prepared : TransactionState}
      {substate : Substate} {meter : Meter} {evm after : Evm fork Meter},
      prepareCreation fork state message.currentTarget = .ok prepared →
      Mcall message prepared substate meter evm → depositCode fork state evm = .ok after →
      Mcreate message state substate meter after)
    (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        Mcall message state substate meter ended.val) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        Mcreate message state substate meter ended.val) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    have callCase : ∀ (message : Message fork) (state : TransactionState) (substate : Substate)
        (meter : Meter) (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
        ∀ ended, processMessage fork message state substate meter held = .ok ended →
          Mcall message state substate meter ended.val := by
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
                   exact Or.inl ⟨‹_›, rfl,
                     by first | rfl | (split <;> first | rfl | contradiction)⟩))
              (frame ?_ hpa hrun)
            rintro caller' message' lt ⟨c, used⟩ hrun'
            dsimp only at hrun'
            unfold ChildRelByKind
            split at hrun'
            · rename_i ht
              simp only [ht]
              exact (ih message'.gas (by omega)).1 message' caller'.state _ _ _ rfl ⟨c, used⟩
                hrun'
            · rename_i ht
              simp only [ht]
              exact (ih message'.gas (by omega)).2 message' caller'.state _ _ _ rfl ⟨c, used⟩
                hrun'
        · simp only [hpa] at hdo
          split at hdo
          · cases hdo
            exact call (by first
                | exact Or.inr ⟨‹message.shouldTransferValue = true ∧ message.value ≠ 0›,
                    Base.mapError_ok_iff.mp hm,
                    by first | rfl | (split <;> first | rfl | contradiction)⟩
                | (cases hm
                   exact Or.inl ⟨‹_›, rfl,
                     by first | rfl | (split <;> first | rfl | contradiction)⟩))
              (skip _ hpa (.inl ‹_›))
          · split at hdo
            · rename_i after hrp
              cases hdo
              exact call (by first
                | exact Or.inr ⟨‹message.shouldTransferValue = true ∧ message.value ≠ 0›,
                    Base.mapError_ok_iff.mp hm,
                    by first | rfl | (split <;> first | rfl | contradiction)⟩
                | (cases hm
                   exact Or.inl ⟨‹_›, rfl,
                     by first | rfl | (split <;> first | rfl | contradiction)⟩))
                (precompile hpa (Bool.eq_false_iff.mpr ‹_›) hrp)
            · rename_i hnone
              cases hdo
              exact call (by first
                | exact Or.inr ⟨‹message.shouldTransferValue = true ∧ message.value ≠ 0›,
                    Base.mapError_ok_iff.mp hm,
                    by first | rfl | (split <;> first | rfl | contradiction)⟩
                | (cases hm
                   exact Or.inl ⟨‹_›, rfl,
                     by first | rfl | (split <;> first | rfl | contradiction)⟩))
                (skip _ hpa (.inr (by split at hnone <;> first | exact hnone | contradiction)))
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

/-- Every successful call satisfies a relation `Mcall`, and every creation a relation `Mcreate`.

That holds at every fork.

The relation `R` of frames must be reflexive and transitive, and keep the invariant `Inv`.

It must hold of each exceptional halt, each stop and each precompile.

Each of these starts from a frame with the invariant.

Each step from a frame with the invariant must keep `R`.

It may use `Mcall` for the calls it sends, and `Mcreate` for the creations.

A call must satisfy `Mcall` after its rollback, when its frame ends related to its start frame.

That frame starts from the state and substate before or after the transfer of value.

A call may use that relation only when its start frame has the invariant.

After its deposit of code, a creation must satisfy `Mcreate` when its init code satisfies `Mcall`.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
theorem processMessage_rel_byKind [LawfulGasMeter Meter]
    {R : Evm fork Meter → Evm fork Meter → Prop} {Inv : Evm fork Meter → Prop}
    {Mcall Mcreate : Message fork → TransactionState → Substate → Meter → Evm fork Meter → Prop}
    (refl : ∀ evm, R evm evm) (trans : ∀ {a b c}, R a b → R b c → R a c)
    (keeps : ∀ {a b}, Inv a → R a b → Inv b)
    (halt : ∀ evm error, Inv evm → R evm (exceptionalHalt evm error))
    (steps : ∀ {evm result}, Inv evm → step fork evm = .ok result →
      StepResult.Keeps R (ChildRelByKind Mcall Mcreate) evm result)
    (stop : ∀ evm : Evm fork Meter, Inv evm → R evm { evm with running := false })
    (precompile : ∀ {address : Nat} {evm after : Evm fork Meter},
      runPrecompile fork address evm = some after → Inv evm → R evm after)
    (call : ∀ {message : Message fork} {state entry : TransactionState}
      {substate entrySubstate : Substate} {meter : Meter} {ended : Evm fork Meter},
      Entered fork message state substate entry entrySubstate →
      (Inv (startFrame message entry entrySubstate meter) →
        R (startFrame message entry entrySubstate meter) ended) →
      Mcall message state substate meter (rollbackOnError state ended))
    (create : ∀ {message : Message fork} {state prepared : TransactionState}
      {substate : Substate} {meter : Meter} {evm after : Evm fork Meter},
      prepareCreation fork state message.currentTarget = .ok prepared →
      Mcall message prepared substate meter evm → depositCode fork state evm = .ok after →
      Mcreate message state substate meter after)
    (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        Mcall message state substate meter ended.val) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        Mcreate message state substate meter ended.val) :=
  processMessage_frame_byKind (F := fun a b => Inv a → R a b)
    (fun runs _ h hinv =>
      rel_runFrame refl trans keeps halt steps (fun caller message lt ended _ hran =>
        runs caller message lt ended hran) hinv h)
    (fun evm _ _ hinv => stop evm hinv) (fun _ _ h hinv => precompile h hinv) call create n

/-- A relation of messages, as a relation of a caller and a child, is the same for both kinds. -/
theorem childRelByKind_self
    (M : Message fork → TransactionState → Substate → Meter → Evm fork Meter → Prop) :
    ChildRelByKind M M = ChildRel M := by
  funext caller message ended
  unfold ChildRelByKind
  split <;> rfl

/-- A relation of a caller and a child gives one for weaker relations of calls and creations. -/
theorem ChildRelByKind.mono
    {Mcall Mcreate Mcall' Mcreate' :
      Message fork → TransactionState → Substate → Meter → Evm fork Meter → Prop}
    (hcall : ∀ message state substate meter ended,
      Mcall message state substate meter ended → Mcall' message state substate meter ended)
    (hcreate : ∀ message state substate meter ended,
      Mcreate message state substate meter ended → Mcreate' message state substate meter ended)
    {caller : Evm fork Meter} {message : Message fork} {ended : Evm fork Meter}
    (h : ChildRelByKind Mcall Mcreate caller message ended) :
    ChildRelByKind Mcall' Mcreate' caller message ended := by
  revert h
  unfold ChildRelByKind ChildRel
  split
  · exact hcall _ _ _ _ _
  · exact hcreate _ _ _ _ _

/-- Every successful call and creation satisfies a relation `M` of messages, at every fork.

The relation `R` of frames must be reflexive and transitive, and keep the invariant `Inv`.

It must hold of each exceptional halt, each stop and each precompile.

Each of these starts from a frame with the invariant.

Each step from a frame with the invariant must keep `R`, given `M` for the messages it sends.

A call must satisfy `M` after its rollback, when its frame ends related to its start frame.

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
    (call : ∀ {message : Message fork} {state entry : TransactionState}
      {substate entrySubstate : Substate} {meter : Meter} {ended : Evm fork Meter},
      Entered fork message state substate entry entrySubstate →
      (Inv (startFrame message entry entrySubstate meter) →
        R (startFrame message entry entrySubstate meter) ended) →
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
        M message state substate meter ended.val) :=
  processMessage_rel_byKind refl trans keeps halt
    (fun hinv h => childRelByKind_self M ▸ steps hinv h) stop precompile call create n

end EthLib.Execution.Evm
