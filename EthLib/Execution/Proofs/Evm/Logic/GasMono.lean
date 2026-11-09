module

public import EthLib.Execution.Proofs.Evm.Logic.Symbolic
public import EthLib.Execution.Proofs.Evm.Interpreter

/-!
# Proofs: steps that are monotone in gas

The facts here are for the meter of one counter of gas, the meter of every fork before Glamsterdam.

At a later fork they hold of that meter, not of the meter of the fork.

A frame with `k` more gas is the same frame, with `k` added to its gas.

An instruction is monotone in gas when, on every frame, it fails, or it gives a frame `b`.

In that second case, the instruction on the frame with `k` more gas gives `b` with `k` more gas.

A frame that halts with an error fails, and so does a frame that reverts.

A frame is monotone in gas when the same holds of the step from every frame with less gas than it.

The triples here are over the steps from frames that are monotone in gas.

Each such triple is a triple over the steps of the logic.

GAS is not monotone in gas, since it pushes the gas left.

A step that sends a message, as a call or a creation does, is no step of the logic.
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

/-- An instruction that, on every frame, fails, or gives a frame `b`.

On that frame with `k` more gas, it then gives `b` with `k` more gas. -/
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

/-- A frame of a code with some gas, with `k` more gas, is the frame of the code with `k` more. -/
theorem At.addGas {evm : Evm fork Nat}
    (h : At code message pc stack memory gas state substate returnData evm) (k : Nat) :
    At code message pc stack memory (gas + k) state substate returnData (addGas k evm) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, by simp [h7], h8, h9, h10, h11, h12, h13⟩

end EthLib.Execution.Evm.Logic
