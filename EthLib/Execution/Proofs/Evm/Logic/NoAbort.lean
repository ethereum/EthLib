module

public import EthLib.Execution.Proofs.Evm.Logic.RunMono

/-!
# Proofs: runs with less gas that never abort

The facts here are for the meter of one counter of gas, the meter of every fork before Glamsterdam.

At a later fork they hold of that meter, not of the meter of the fork.

The loop of the interpreter returns an error only for an error that aborts the whole run.

An error of the state aborts, and so does an opcode with no instruction.

An encoding error aborts too, and so does a fork with no specification.

An instruction that runs out of gas or of stack halts its frame instead.

So do a jump to an invalid destination and a write in a static frame.

That halt is no error of the loop.

A triple over steps from frames monotone in gas says how a run with less gas ends on success.

With less gas, a step may still fail with any error.

The steps here also ask that no step from a frame with less gas fails with an error that aborts.

Take a specification over these steps from a frame, with every gas from some bound on.

Then a run of the frame never aborts.

With any gas, also below the bound, the loop of the interpreter returns a frame, never an error.

Every instruction of `Logic/RunMono.lean` never aborts, except SSTORE, whose write may fail.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork}

/-! ## Results that do not abort -/

/-- The result `r` is no error that aborts the run. -/
def NoAbort {α : Type} (r : Except EvmError α) : Prop := ∀ e, r = .error e → e.aborts = false

/-- A success does not abort. -/
theorem NoAbort.ok {α : Type} (a : α) : NoAbort (.ok a : Except EvmError α) :=
  fun _ h => by cases h

/-- A sequence of two results that do not abort does not abort. -/
theorem NoAbort.bind {α β : Type} {x : Except EvmError α} {f : α → Except EvmError β}
    (hx : NoAbort x) (hf : ∀ a, NoAbort (f a)) : NoAbort (x >>= f) := by
  intro e h
  cases hx' : x with
  | error e' =>
    rw [hx'] at h
    cases h
    exact hx _ hx'
  | ok a =>
    rw [hx'] at h
    exact hf a e h

/-- A map of a result that does not abort does not abort. -/
theorem NoAbort.map {α β : Type} {x : Except EvmError α} (f : α → β) (hx : NoAbort x) :
    NoAbort (f <$> x) := by
  intro e h
  cases hx' : x with
  | error e' =>
    rw [hx'] at h
    cases h
    exact hx _ hx'
  | ok a =>
    rw [hx'] at h
    cases h

/-- A pop fails only with a stack underflow. -/
theorem noAbort_popWord (evm : Evm fork Nat) : NoAbort (popWord evm) := by
  rintro e h
  rcases hs : evm.stack with ⟨_ | ⟨x, rest⟩, hp⟩ <;>
    simp [popWord, Stack.pop, hs, bind, Except.bind, pure, Except.pure] at h
  subst h
  rfl

/-- A push fails only with a stack overflow. -/
theorem noAbort_pushWord (evm : Evm fork Nat) (x : U256) : NoAbort (pushWord evm x) := by
  rintro e h
  simp only [pushWord, Stack.push, bind, Except.bind] at h
  split at h
  · rename_i heq
    cases h
    split at heq
    · cases heq
      rfl
    · cases heq
  · cases h

/-- A charge fails only out of gas. -/
theorem noAbort_chargeGas (evm : Evm fork Nat) (cost : Nat) : NoAbort (chargeGas evm cost) := by
  rintro e h
  simp only [chargeGas, GasMeter.charge, bind, Except.bind] at h
  split at h
  · rename_i heq
    cases h
    split at heq
    · cases heq
      rfl
    · cases heq
  · cases h

/-- A charge of gas and of the growth of memory fails only out of gas. -/
theorem noAbort_chargeGasAndMemory (evm : Evm fork Nat) (cost : Nat)
    (ranges : List (U256 × U256)) : NoAbort (chargeGasAndMemory evm cost ranges) :=
  NoAbort.bind (noAbort_chargeGas _ _) fun _ => NoAbort.ok _

/-- PUSHn fails only out of gas or of stack. -/
theorem noAbort_pushN (n : Fin 33) (evm : Evm fork Nat) : NoAbort (pushN n evm) :=
  NoAbort.bind (noAbort_chargeGas _ _) fun _ =>
    NoAbort.bind (noAbort_pushWord _ _) fun _ => NoAbort.ok _

/-- A one-operand instruction of the stack fails only out of gas or of stack. -/
theorem noAbort_unaryOp (cost : Nat) (f : U256 → U256) (evm : Evm fork Nat) :
    NoAbort (unaryOp cost f evm) :=
  NoAbort.bind (noAbort_popWord _) fun _ =>
    NoAbort.bind (noAbort_chargeGas _ _) fun _ =>
      NoAbort.bind (noAbort_pushWord _ _) fun _ => NoAbort.ok _

/-- A two-operand instruction of the stack fails only out of gas or of stack. -/
theorem noAbort_binaryOp (cost : Nat) (f : U256 → U256 → U256) (evm : Evm fork Nat) :
    NoAbort (binaryOp cost f evm) :=
  NoAbort.bind (noAbort_popWord _) fun _ =>
    NoAbort.bind (noAbort_popWord _) fun _ =>
      NoAbort.bind (noAbort_chargeGas _ _) fun _ =>
        NoAbort.bind (noAbort_pushWord _ _) fun _ => NoAbort.ok _

/-- POP fails only out of gas or of stack. -/
theorem noAbort_pop (evm : Evm fork Nat) : NoAbort (popStep evm) :=
  NoAbort.bind (noAbort_popWord _) fun _ =>
    NoAbort.bind (noAbort_chargeGas _ _) fun _ => NoAbort.ok _

/-- JUMPDEST fails only out of gas. -/
theorem noAbort_jumpdest (evm : Evm fork Nat) : NoAbort (jumpdestStep evm) :=
  NoAbort.bind (noAbort_chargeGas _ _) fun _ => NoAbort.ok _

/-- CALLDATALOAD fails only out of gas or of stack. -/
theorem noAbort_calldataload (evm : Evm fork Nat) : NoAbort (calldataloadStep evm) :=
  NoAbort.bind (noAbort_popWord _) fun _ =>
    NoAbort.bind (noAbort_chargeGas _ _) fun _ =>
      NoAbort.bind (noAbort_pushWord _ _) fun _ => NoAbort.ok _

/-- MLOAD fails only out of gas or of stack. -/
theorem noAbort_mload (evm : Evm fork Nat) : NoAbort (mloadStep evm) :=
  NoAbort.bind (noAbort_popWord _) fun _ =>
    NoAbort.bind (noAbort_chargeGasAndMemory _ _ _) fun _ =>
      NoAbort.bind (noAbort_pushWord _ _) fun _ => NoAbort.ok _

/-- MSTORE fails only out of gas or of stack. -/
theorem noAbort_mstore (evm : Evm fork Nat) : NoAbort (mstoreStep evm) :=
  NoAbort.bind (noAbort_popWord _) fun _ =>
    NoAbort.bind (noAbort_popWord _) fun _ =>
      NoAbort.bind (noAbort_chargeGasAndMemory _ _ _) fun _ => NoAbort.ok _

/-- KECCAK256 fails only out of gas or of stack. -/
theorem noAbort_keccak256 (evm : Evm fork Nat) : NoAbort (keccak256Step evm) :=
  NoAbort.bind (noAbort_popWord _) fun _ =>
    NoAbort.bind (noAbort_popWord _) fun _ =>
      NoAbort.bind (noAbort_chargeGasAndMemory _ _ _) fun _ =>
        NoAbort.bind (noAbort_pushWord _ _) fun _ => NoAbort.ok _

/-- SLOAD fails only out of gas or of stack. -/
theorem noAbort_sload (evm : Evm fork Nat) : NoAbort (sloadStep evm) :=
  NoAbort.bind (noAbort_popWord _) fun _ =>
    NoAbort.bind (noAbort_chargeGas _ _) fun _ =>
      NoAbort.bind (noAbort_pushWord _ _) fun _ => NoAbort.ok _

/-- RETURN fails only out of gas or of stack. -/
theorem noAbort_return (evm : Evm fork Nat) : NoAbort (returnStep evm) :=
  NoAbort.bind (noAbort_popWord _) fun _ =>
    NoAbort.bind (noAbort_popWord _) fun _ =>
      NoAbort.bind (noAbort_chargeGasAndMemory _ _ _) fun _ => NoAbort.ok _

/-- STOP never fails. -/
theorem noAbort_stop (evm : Evm fork Nat) : NoAbort (stopStep evm) := NoAbort.ok _

/-- An error that halts only its frame is no error that aborts. -/
theorem NoAbort.error {α : Type} {e : EvmError} (h : e.aborts = false) :
    NoAbort (.error e : Except EvmError α) :=
  fun _ he => by cases he; exact h

/-- A three-operand instruction of the stack fails only out of gas or of stack. -/
theorem noAbort_ternaryOp (cost : Nat) (f : U256 → U256 → U256 → U256) (evm : Evm fork Nat) :
    NoAbort (ternaryOp cost f evm) :=
  NoAbort.bind (noAbort_popWord _) fun _ =>
    NoAbort.bind (noAbort_popWord _) fun _ =>
      NoAbort.bind (noAbort_popWord _) fun _ =>
        NoAbort.bind (noAbort_chargeGas _ _) fun _ =>
          NoAbort.bind (noAbort_pushWord _ _) fun _ => NoAbort.ok _

/-- EXP fails only out of gas or of stack. -/
theorem noAbort_exp (evm : Evm fork Nat) : NoAbort (expStep fork evm) :=
  NoAbort.bind (noAbort_popWord _) fun _ =>
    NoAbort.bind (noAbort_popWord _) fun _ =>
      NoAbort.bind (noAbort_chargeGas _ _) fun _ =>
        NoAbort.bind (noAbort_pushWord _ _) fun _ => NoAbort.ok _

/-- An instruction that pushes a word of the frame fails only out of gas or of stack. -/
theorem noAbort_readFrame (cost : Nat) (f : Evm fork Nat → U256) (evm : Evm fork Nat) :
    NoAbort (readFrame cost f evm) :=
  NoAbort.bind (noAbort_chargeGas _ _) fun _ =>
    NoAbort.bind (noAbort_pushWord _ _) fun _ => NoAbort.ok _

/-- DUPn fails only out of gas or of stack. -/
theorem noAbort_dupN (n : Fin 16) (evm : Evm fork Nat) : NoAbort (dupN n evm) := by
  refine NoAbort.bind (noAbort_chargeGas _ _) fun b => ?_
  split
  · exact NoAbort.error rfl
  · exact NoAbort.bind (noAbort_pushWord _ _) fun _ => NoAbort.ok _

/-- SWAPn fails only out of gas or of stack. -/
theorem noAbort_swapN (n : Fin 16) (evm : Evm fork Nat) : NoAbort (swapN n evm) := by
  refine NoAbort.bind (noAbort_chargeGas _ _) fun b => ?_
  split
  · split
    · exact NoAbort.error rfl
    · exact NoAbort.ok _
  · exact NoAbort.error rfl

/-- JUMP fails only out of gas or of stack, or at an invalid destination. -/
theorem noAbort_jump (evm : Evm fork Nat) : NoAbort (jumpStep evm) := by
  refine NoAbort.bind (noAbort_popWord _) fun _ => NoAbort.bind (noAbort_chargeGas _ _) fun _ => ?_
  split
  · exact NoAbort.ok _
  · exact NoAbort.error rfl

/-- JUMPI fails only out of gas or of stack, or at an invalid destination. -/
theorem noAbort_jumpi (evm : Evm fork Nat) : NoAbort (jumpiStep evm) := by
  refine NoAbort.bind (noAbort_popWord _) fun _ => NoAbort.bind (noAbort_popWord _) fun _ =>
    NoAbort.bind (noAbort_chargeGas _ _) fun _ => ?_
  split
  · exact NoAbort.ok _
  · split
    · exact NoAbort.ok _
    · exact NoAbort.error rfl

/-- The pops of the topics of a log fail only with a stack underflow. -/
theorem noAbort_popTopics (n : Nat) : ∀ evm : Evm fork Nat, NoAbort (popTopics evm n) := by
  induction n with
  | zero => exact fun _ => NoAbort.ok _
  | succ n ih =>
    exact fun _ => NoAbort.bind (noAbort_popWord _) fun _ =>
      NoAbort.bind (ih _) fun _ => NoAbort.ok _

/-- LOGn fails only out of gas or of stack, or in a static frame. -/
theorem noAbort_log (n : Nat) (evm : Evm fork Nat) : NoAbort (logStep n evm) := by
  refine NoAbort.bind (noAbort_popWord _) fun _ => NoAbort.bind (noAbort_popWord _) fun _ =>
    NoAbort.bind (noAbort_popTopics _ _) fun _ =>
      NoAbort.bind (noAbort_chargeGasAndMemory _ _ _) fun _ => ?_
  split
  · exact NoAbort.error rfl
  · exact NoAbort.ok _

/-- REVERT fails only out of gas or of stack. -/
theorem noAbort_revert (evm : Evm fork Nat) : NoAbort (revertStep evm) :=
  NoAbort.bind (noAbort_return evm) fun _ => NoAbort.ok _

/-! ## Steps that do not abort with less gas -/

/-- From every frame with less gas than `evm`, the step is no error that aborts. -/
def NoAbortLow (evm : Evm fork Nat) : Prop :=
  ∀ k low, evm = addGas k low → NoAbort (step fork low)

/-- A step from a frame that is monotone in gas, and from which no step with less gas aborts. -/
def StepGA (fork : Fork) (evm after : Evm fork Nat) : Prop := StepG fork evm after ∧ NoAbortLow evm

/-- A triple over the steps from frames that are monotone in gas and do not abort with less gas. -/
abbrev HoareGA (fork : Fork) (P Q : Evm fork Nat → Prop) : Prop := Triple (StepGA fork) P Q

/-- A specification over the steps from frames monotone in gas that do not abort with less gas. -/
def SpecGA (fork : Fork) (P Q : Evm fork Nat → Prop) : Prop :=
  HoareGA fork P fun evm => evm.running = false ∧ Q evm

/-- A triple over these steps is a triple over the steps from frames that are monotone in gas. -/
theorem HoareGA.toG {P Q : Evm fork Nat → Prop} (h : HoareGA fork P Q) : HoareG fork P Q :=
  fun evm hp =>
    let ⟨after, hr, hq⟩ := h evm hp
    ⟨after, hr.mono And.left, hq⟩

/-- A specification over these steps is one over the steps from frames that are monotone in gas. -/
theorem SpecGA.toG {P Q : Evm fork Nat → Prop} (h : SpecGA fork P Q) : SpecG fork P Q :=
  HoareGA.toG h

/-- A triple to a frame from which the specification holds. -/
theorem SpecGA.seq {P Q R : Evm fork Nat → Prop} (first : HoareGA fork P Q)
    (second : SpecGA fork Q R) : SpecGA fork P R := Triple.seq first second

/-- Consequence for a specification over these steps. -/
theorem SpecGA.consequence {P P' Q Q' : Evm fork Nat → Prop} (h : SpecGA fork P Q)
    (pre : ∀ evm, P' evm → P evm) (post : ∀ evm, Q evm → Q' evm) : SpecGA fork P' Q' :=
  Triple.consequence h pre fun evm ⟨hs, hq⟩ => ⟨hs, post evm hq⟩

variable {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}
  {returnData : ByteArray}

/-- The rule of an opcode whose instruction never aborts.

On each frame of the rule, the instruction must also follow that with less gas.

It comes from the instruction that its byte runs on a frame of the code. -/
theorem At.ruleGA_of_follows {byte : UInt8} {op : Op}
    {run : Evm fork Nat → Except EvmError (Evm fork Nat)} {post : Evm fork Nat → Prop}
    (hlt : pc < code.size) (hbyte : code[pc] = byte) (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction fork op = some run)
    (mono : ∀ evm, At code message pc stack memory gas state substate returnData evm →
      ∀ k low, evm = Logic.addGas k low → Follows k (run low) (run evm))
    (never : ∀ evm, NoAbort (run evm))
    (h : ∀ evm, At code message pc stack memory gas state substate returnData evm →
      ∃ after, run evm = .ok after ∧ post after) :
    HoareGA fork (At code message pc stack memory gas state substate returnData) post := by
  apply Triple.of_step
  intro evm hp
  obtain ⟨after, ok, hpost⟩ := h evm hp
  have hmono := mono evm hp
  have running := hp.2.2.2.2.2.2.2.1
  obtain ⟨hcode, -, -, hpc, -⟩ := hp
  subst hcode hpc
  have hdec : Op.ofByte fork evm.code[evm.pc] = some op := by rw [hbyte]; exact decoded
  refine ⟨after, ⟨⟨Step.of_instruction running hlt hdec hrun ok,
    gasMono_of_follows hlt hdec hrun hmono⟩, ?_⟩, hpost⟩
  rintro k low hlow
  have hc : low.code = evm.code := by rw [hlow]; rfl
  have hp' : low.pc = evm.pc := by rw [hlow]; rfl
  have hlt' : low.pc < low.code.size := by rw [hc, hp']; exact hlt
  have hdec' : Op.ofByte fork low.code[low.pc] = some op := by simp only [hc, hp', hdec]
  rw [step_of_instruction hlt' hdec' hrun]
  exact NoAbort.map _ (never low)

/-- The rule of an opcode whose instruction is monotone in gas and never aborts.

It comes from the instruction that its byte runs on a frame of the code. -/
theorem At.ruleGA {byte : UInt8} {op : Op}
    {run : Evm fork Nat → Except EvmError (Evm fork Nat)} {post : Evm fork Nat → Prop}
    (hlt : pc < code.size) (hbyte : code[pc] = byte) (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction fork op = some run) (mono : RunMono run) (never : ∀ evm, NoAbort (run evm))
    (h : ∀ evm, At code message pc stack memory gas state substate returnData evm →
      ∃ after, run evm = .ok after ∧ post after) :
    HoareGA fork (At code message pc stack memory gas state substate returnData) post :=
  At.ruleGA_of_follows hlt hbyte decoded hrun (fun _ _ k low h => by subst h; exact mono low k)
    never h

/-! ## The loop never returns an error -/

section Loop

variable {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- A chain of these steps from `low` with `k` more gas to a stopped frame.

The loop then runs `low` to a frame, never to an error.

With less gas, each step halts the frame, or follows the chain. -/
theorem no_error_of_reaches {hi z : Evm fork Nat} (hr : Reaches (StepGA fork) hi z)
    (hz : z.running = false) :
    ∀ (k : Nat) (low : Evm fork Nat), hi = addGas k low →
      ∀ (within : GasMeter.gasHeld low.gas ≤ bound) (e : EvmError),
        Evm.runFrame (step fork) (step_decreases fork) bound runChild low within ≠ .error e := by
  induction hr with
  | refl =>
    rintro k low rfl within e h
    rw [runFrame_of_running_eq_false (by simpa using hz)] at h
    cases h
  | step hs _ ih =>
    rintro k low rfl within e h
    obtain ⟨⟨hstep, mono⟩, never⟩ := hs
    have running : low.running = true := by simpa using hstep.running
    rcases mono k low rfl with (⟨e', he⟩ | ⟨b, hb, hbr, -⟩) | ⟨b, hb, hh⟩
    · rw [runFrame_of_step_eq_error running he (never k low rfl e' he)] at h
      cases h
    · rw [runFrame_of_step_eq_next running hb, runFrame_of_running_eq_false hbr] at h
      cases h
    · rw [runFrame_of_step_eq_next running hb] at h
      cases hstep with
      | next _ hn =>
        rw [hh] at hn
        cases hn
        exact ih hz k b rfl _ e h
      | halt _ hn _ =>
        rw [hh] at hn
        cases hn

/-- A frame of a code that meets a specification over these steps with every gas from `B` on.

The loop runs the frame with any gas, also below `B`, to a frame, never to an error. -/
theorem no_error {B : Nat} {Q : Nat → Evm fork Nat → Prop}
    (h : ∀ g, B ≤ g →
      SpecGA fork (At code message pc stack memory g state substate returnData) (Q g))
    {evm : Evm fork Nat} (start : At code message pc stack memory gas state substate returnData evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) (e : EvmError) :
    Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within ≠ .error e := by
  obtain ⟨z, hr, hz, -⟩ := h (gas + B) (Nat.le_add_left B gas) _ (start.addGas B)
  exact no_error_of_reaches hr hz B evm rfl within e

end Loop

end EthLib.Execution.Evm.Logic
