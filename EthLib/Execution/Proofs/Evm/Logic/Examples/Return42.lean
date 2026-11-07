module

public import EthLib.Execution.Proofs.Evm.Logic.Symbolic
public import EthLib.Execution.Proofs.Evm.Instructions.MemoryData

/-!
# Proofs: a contract that returns 42

This example shows that the logic proves the specification of a whole contract.

The bytecode `0x602a60005260206000f3` is the program `mstore(0, 42) return(0, 32)`.

- At 0, `60 2a` is PUSH1 0x2a.
- At 2, `60 00` is PUSH1 0.
- At 4, `52` is MSTORE.
- At 5, `60 20` is PUSH1 0x20.
- At 7, `60 00` is PUSH1 0.
- At 9, `f3` is RETURN.

It writes the word 42 at offset 0 of memory, then returns those 32 bytes.

It costs 18 gas: four pushes of 3, an MSTORE of 3, and the growth of memory to one word for 3.

Its RETURN costs 0, and grows nothing.

The prices are those of the gas constants of the library, with one counter of gas.

That is the meter of every fork before Glamsterdam.

The specification: a frame starts this code at the program counter 0, with an empty stack.

With empty memory and at least 18 gas, it halts normally.

It returns the 32 big-endian bytes of 42, keeps 18 gas less, and keeps its state and substate.

The proof runs the code one opcode at a time, then carries the result to the interpreter loop.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic.Return42

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork}

/-- The bytecode of `mstore(0, 42) return(0, 32)`. -/
def CODE : ByteArray := ⟨#[0x60, 0x2a, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3]⟩

/-- A running frame of the code, at a program counter, with a stack, a memory and some gas. -/
abbrev At (pc : Nat) (stack : List U256) (memory : ByteArray) (gas : Nat)
    (state : State.TransactionState) (substate : Substate) : Evm fork Nat → Prop :=
  Logic.At CODE pc stack memory gas state substate

/-- The memory after MSTORE: the word 42 on 32 bytes. -/
def MEMORY : ByteArray := memoryWrite (memoryExtend .empty 32) 0 (wordBytes 42)

variable {state : State.TransactionState} {substate : Substate}

/-- The MSTORE of the code writes 42 to empty memory, which grows to one word, for 6 gas. -/
theorem mstore {gas : Nat} (hgas : 6 ≤ gas) :
    Hoare fork (At 4 [0, 42] .empty gas state substate)
      (At 5 [] MEMORY (gas - 6) state substate) := by
  apply Hoare.of_step
  rintro ⟨pc, ⟨items, hitems⟩, memory, code, jumps, g, running, message, output, returnData,
    st, ss, error⟩ ⟨hcode, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  dsimp only at hcode hpc hst hmem hg hrun herr hs hss
  subst hcode hpc hst hmem hg hrun herr hs hss
  refine ⟨⟨5, ⟨[], Nat.zero_le _⟩, MEMORY, CODE, jumps, g - 6, true, message, output,
      returnData, st, ss, none⟩,
    Step.of_code (code := CODE) (pc := 4) (byte := 0x52) rfl rfl rfl (by decide) (by decide)
      (ofByte_of_decode (op := .mstore) rfl rfl) instruction_mstore ?_,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hcharge : ¬g < OPCODE_MSTORE_BASE + 3 := by
    simp only [OPCODE_MSTORE_BASE, VERY_LOW]
    omega
  -- Memory grows from no word to one word, for 3 gas.
  have hext : extendMemory ByteArray.empty.size [((0 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    decide
  rw [mstoreStep_cons (rest := []) rfl]
  simp only [hext, GasMeter.charge, hcharge, ↓reduceIte, Except.map]
  rfl

/-- The 32 bytes that the code returns: the word 42, big-endian. -/
theorem memoryReadBytes_memory :
    memoryReadBytes (memoryExtend MEMORY 0) 0 32 = wordBytes 42 := by
  decide

/-- What the run ends with: a normal halt that returns 42, with the gas, state and substate. -/
def Returned (gas : Nat) (state : State.TransactionState) (substate : Substate)
    (evm : Evm fork Nat) : Prop :=
  evm.error = none ∧ evm.output = wordBytes 42 ∧ evm.gas = gas ∧ evm.state = state ∧
    evm.substate = substate

/-- The RETURN of the code stops the frame with the word of memory as its output, for no gas. -/
theorem «return» {gas : Nat} :
    Spec fork (At 9 [0, 32] MEMORY gas state substate) (Returned gas state substate) := by
  apply Hoare.of_step
  rintro ⟨pc, ⟨items, hitems⟩, memory, code, jumps, g, running, message, output, returnData,
    st, ss, error⟩ ⟨hcode, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  dsimp only at hcode hpc hst hmem hg hrun herr hs hss
  subst hcode hpc hst hmem hg hrun herr hs hss
  refine ⟨⟨9, ⟨[], Nat.zero_le _⟩, memoryExtend MEMORY 0, CODE, jumps, g, false, message,
      memoryReadBytes (memoryExtend MEMORY 0) 0 32, returnData, st, ss, none⟩,
    Step.of_code (code := CODE) (pc := 9) (byte := 0xf3) rfl rfl rfl (by decide) (by decide)
      (ofByte_of_decode (op := .«return») rfl rfl) instruction_return ?_,
    rfl, rfl, memoryReadBytes_memory, rfl, rfl, rfl⟩
  -- Memory already holds the word, so it does not grow.
  have hext : extendMemory MEMORY.size [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    decide
  simp only [returnStep, haltWithOutput, popWord, Stack.pop, chargeGasAndMemory, hext, chargeGas,
    GasMeter.charge, Nat.not_lt_zero, Nat.add_zero, ↓reduceIte, Nat.sub_zero, bind, Except.bind,
    pure, Except.pure]
  rfl

/-- The specification of the code: the frame halts normally and returns the word 42.

It starts at the program counter 0, with an empty stack, empty memory and at least 18 gas.

It keeps 18 gas less, and keeps its state and substate. -/
theorem spec {gas : Nat} (hgas : 18 ≤ gas) :
    Spec fork (At 0 [] .empty gas state substate) (Returned (gas - 18) state substate) := by
  have p1 := push1 (code := CODE) (fork := fork) (state := state) (substate := substate) (pc := 0)
    (stack := [])
    (memory := .empty) (gas := gas) (byte := 0x2a) (by decide) rfl rfl (by omega) (by decide)
  have p2 := push1 (code := CODE) (fork := fork) (state := state) (substate := substate) (pc := 2)
    (stack := [42]) (memory := .empty) (gas := gas - 3) (byte := 0x00) (by decide) rfl rfl
    (by omega) (by decide)
  have m := mstore (fork := fork) (state := state) (substate := substate) (gas := gas - 3 - 3)
    (by omega)
  have p3 := push1 (code := CODE) (fork := fork) (state := state) (substate := substate) (pc := 5)
    (stack := [])
    (memory := MEMORY) (gas := gas - 3 - 3 - 6) (byte := 0x20) (by decide) rfl rfl (by omega)
    (by decide)
  have p4 := push1 (code := CODE) (fork := fork) (state := state) (substate := substate) (pc := 7)
    (stack := [32]) (memory := MEMORY) (gas := gas - 3 - 3 - 6 - 3) (byte := 0x00) (by decide)
    rfl rfl (by omega) (by decide)
  have r := «return» (fork := fork) (state := state) (substate := substate)
    (gas := gas - 3 - 3 - 6 - 3 - 3)
  have hsum : gas - 3 - 3 - 6 - 3 - 3 = gas - 18 := by omega
  rw [hsum] at r
  exact (p1.seq p2).seq m |>.seq p3 |>.seq p4 |> fun h => Spec.seq h r

/-- The loop of the interpreter runs the code to its specification.

It holds for every bound on the gas of messages and every runner of messages.

The code sends no message. -/
theorem runFrame_spec {gas : Nat} (hgas : 18 ≤ gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At 0 [] .empty gas state substate evm) (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ Returned (gas - 18) state substate stopped :=
  (spec hgas).runFrame start within

end EthLib.Execution.Evm.Logic.Return42
