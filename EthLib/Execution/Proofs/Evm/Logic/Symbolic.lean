module

public import EthLib.Execution.Proofs.Evm.Logic.Triple
public import EthLib.Base.Proofs.Fork
public import EthLib.Execution.Proofs.Evm.Instructions.StackOnly

/-!
# Proofs: steps of straight-line bytecode, one opcode at a time

A proof about bytecode runs it one opcode at a time.

Each step reads the byte at the program counter and decodes its opcode at the fork.

It then runs the instruction of that opcode.

The lemmas here turn that into one equation for each kind of step.

They take the frame as it is, with its fields named, so a proof never unfolds a whole frame.

This keeps the terms of a long run small: each step rewrites a few fields of the last frame.

The equations are for the meter of one counter of gas, `Nat`, of every fork before Glamsterdam.

A rule for an opcode is a triple from one frame of a code to the next, such as `push1`.

A run of straight-line code is a sequence of such rules, so each rule is checked once on its own.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## A step runs the instruction of the byte at the program counter -/

/-- A running frame steps to the frame that the instruction of its opcode gives. -/
theorem Step.of_instruction {evm after : Evm fork Meter} {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)} (running : evm.running = true)
    (h : evm.pc < evm.code.size) (decoded : Op.ofByte fork evm.code[evm.pc] = some op)
    (hrun : instruction fork op = some run) (ok : run evm = .ok after) : Step fork evm after :=
  .next running (by rw [step_of_instruction h decoded hrun, ok]; rfl)

/-- The same step, with the code, the program counter and the byte given apart from the frame.

A proof about a fixed code gives these as facts, so it never rewrites inside the frame. -/
theorem Step.of_code {evm after : Evm fork Meter} {code : ByteArray} {pc : Nat} {byte : UInt8}
    {op : Op} {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (running : evm.running = true) (hcode : evm.code = code) (hpc : evm.pc = pc)
    (hlt : pc < code.size) (hbyte : code[pc] = byte) (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction fork op = some run) (ok : run evm = .ok after) : Step fork evm after := by
  have h : evm.pc < evm.code.size := by rw [hcode, hpc]; exact hlt
  have hb : evm.code[evm.pc] = byte := by
    rw [← hbyte]
    congr 1 <;> first | exact hcode | (subst hcode; exact hpc) | simp [hcode, hpc]
  exact Step.of_instruction running h (hb ▸ decoded) hrun ok

/-- A byte whose opcode dates from Frontier decodes to that opcode at every fork. -/
theorem ofByte_of_decode {byte : UInt8} {op : Op} (h : Op.decode byte = some op)
    (since : op.since = .frontier) : Op.ofByte fork byte = some op := by
  simp only [Op.ofByte, h, Option.filter, since]
  simp [Fork.frontier_le fork]

/-! ## The instruction table -/

/-- PUSHn runs the push of its `n` bytes. -/
theorem instruction_push (n : Fin 33) :
    instruction (Meter := Meter) fork (.push n) = some (pushN n) := by
  simp [instruction, stackOnlyStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- MSTORE runs the store of a word to memory. -/
theorem instruction_mstore : instruction (Meter := Meter) fork .mstore = some mstoreStep := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, HOrElse.hOrElse,
    OrElse.orElse, Option.orElse]

/-- RETURN runs the halt with output. -/
theorem instruction_return : instruction (Meter := Meter) fork .«return» = some returnStep := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-! ## The parts of an instruction, with one counter of gas -/

/-- A charge that the gas covers takes it from the counter. -/
theorem chargeGas_nat {evm : Evm fork Nat} {amount : Nat} (h : amount ≤ evm.gas) :
    chargeGas evm amount = .ok { evm with gas := evm.gas - amount } := by
  simp [chargeGas, GasMeter.charge, Nat.not_lt.mpr h, bind, Except.bind, pure, Except.pure]

omit [GasMeter Meter] in
/-- A push onto a stack that is not full puts the word on top. -/
theorem pushWord_of_lt {evm : Evm fork Meter} {x : U256}
    (h : evm.stack.val.length < STACK_LIMIT) :
    pushWord evm x = .ok { evm with stack := ⟨x :: evm.stack.val, h⟩ } := by
  simp [pushWord, Stack.push, Nat.ne_of_lt h, bind, Except.bind, pure, Except.pure]

omit [GasMeter Meter] in
/-- A pop of a stack with a word on top takes that word. -/
theorem popWord_of_val {evm : Evm fork Meter} {x : U256} {rest : List U256}
    (h : evm.stack.val = x :: rest) :
    popWord evm = .ok (x, { evm with stack := ⟨rest, by
      have := evm.stack.property; rw [h] at this; exact Nat.le_of_succ_le this⟩ }) := by
  unfold popWord Stack.pop
  split
  · rename_i heq
    rw [heq] at h
    cases h
  · rename_i y ys hy heq
    rw [heq] at h
    cases h
    rfl

/-! ## The instructions, with one counter of gas -/

/-- PUSHn, for `n` from 1, with the gas and the room for one word: it pays 3 and pushes `n` bytes.

It then skips those bytes of code.

It is `pushN_of_length_lt` with the charge of one counter of gas worked out. -/
theorem pushN_nat {evm : Evm fork Nat} {n : Fin 33} (hn : n.val ≠ 0)
    (hgas : OPCODE_PUSH ≤ evm.gas) (hstack : evm.stack.val.length < STACK_LIMIT) :
    pushN n evm = .ok { evm with
      stack := ⟨pushData evm.code evm.pc n :: evm.stack.val, hstack⟩,
      gas := evm.gas - OPCODE_PUSH, pc := evm.pc + (1 + n) } := by
  rw [pushN_of_length_lt hstack]
  simp [hn, GasMeter.charge, Nat.not_lt.mpr hgas, Except.map]

/-! ## Rules for the opcodes of a code -/

/-- A running frame of a code, at a program counter, with a stack, a memory and some gas.

It also names the state, the substate and the error of the frame, none. -/
def At (code : ByteArray) (pc : Nat) (stack : List U256) (memory : ByteArray) (gas : Nat)
    (state : State.TransactionState) (substate : Substate) (evm : Evm fork Nat) : Prop :=
  evm.code = code ∧ evm.pc = pc ∧ evm.stack.val = stack ∧ evm.memory = memory ∧
    evm.gas = gas ∧ evm.running = true ∧ evm.error = none ∧ evm.state = state ∧
    evm.substate = substate

variable {state : State.TransactionState} {substate : Substate}

/-- PUSH1 pushes the byte after it and costs 3, with room on the stack. -/
theorem push1 {code : ByteArray} {pc : Nat} {stack : List U256} {memory : ByteArray} {gas : Nat}
    {byte : UInt8} (hlt : pc + 1 < code.size) (hop : code[pc]'(by omega) = 0x60)
    (hbyte : code[pc + 1] = byte) (hgas : 3 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code pc stack memory gas state substate)
      (At code (pc + 2) (BitVec.ofNat 256 byte.toNat :: stack) memory (gas - 3) state
        substate) := by
  apply Hoare.of_step
  rintro evm ⟨hcode, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  have hlen : evm.stack.val.length < STACK_LIMIT := by rw [hst]; exact hstack
  have hg3 : OPCODE_PUSH ≤ evm.gas := by rw [hg]; exact hgas
  refine ⟨_, Step.of_code hrun hcode hpc (by omega) hop
    (ofByte_of_decode (op := .push 1) rfl rfl) (instruction_push 1)
    (pushN_nat (n := 1) (by decide) hg3 hlen), ?_⟩
  refine ⟨hcode, ?_, ?_, hmem, ?_, hrun, herr, hs, hss⟩
  · simp [hpc]
  · simp [hst, pushData, bufferRead, hcode, hpc, Base.byteAt, hlt, hbyte, Base.bytesToNat]
  · simp [hg, OPCODE_PUSH, VERY_LOW]

end EthLib.Execution.Evm.Logic
