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

The equations are for the meter of one counter of gas, the meter of every fork before Glamsterdam.

At a later fork they hold of that meter, not of the meter of the fork.

A rule for an opcode, such as the rule for PUSH1, is a triple from one frame of a code to the next.

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
  subst hcode hpc
  exact Step.of_instruction running hlt (by rw [hbyte]; exact decoded) hrun ok

/-- A byte whose opcode a fork has decodes to that opcode at the fork. -/
theorem ofByte_of_decode {byte : UInt8} {op : Op} (h : Op.decode byte = some op)
    (since : op.since ≤ fork) : Op.ofByte fork byte = some op := by
  simp [Op.ofByte, h, Option.filter, since]

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

/-! ## The instructions, with one counter of gas -/

/-- PUSHn, for `n` from 1, with the gas and the room for one word: it pays 3 and pushes `n` bytes.

It then skips those bytes of code. -/
theorem pushN_nat {evm : Evm fork Nat} {n : Fin 33} (hn : n.val ≠ 0)
    (hgas : OPCODE_PUSH ≤ evm.gas) (hstack : evm.stack.val.length < STACK_LIMIT) :
    pushN n evm = .ok { evm with
      stack := ⟨pushData evm.code evm.pc n :: evm.stack.val, hstack⟩,
      gas := evm.gas - OPCODE_PUSH, pc := evm.pc + (1 + n) } := by
  rw [pushN_of_length_lt hstack]
  simp [hn, GasMeter.charge, Nat.not_lt.mpr hgas, Except.map]

/-! ## Rules for the opcodes of a code -/

/-- A running frame of a code, at a program counter, with a stack, a memory and some gas.

It holds the flags of the jump destinations of its code, and its message.

It also names the state, the substate and the error of the frame, none.

Its output is empty.

The interpreter sets the code, the flags and the message when it starts a frame.

No step changes them, so they stay the same along a run. -/
def At (code : ByteArray) (message : Message fork) (pc : Nat) (stack : List U256)
    (memory : ByteArray) (gas : Nat) (state : State.TransactionState) (substate : Substate)
    (evm : Evm fork Nat) : Prop :=
  evm.code = code ∧ evm.validJumpDestinations = validJumpDestinations code ∧
    evm.message = message ∧ evm.pc = pc ∧ evm.stack.val = stack ∧ evm.memory = memory ∧
    evm.gas = gas ∧ evm.running = true ∧ evm.error = none ∧ evm.output = .empty ∧
    evm.state = state ∧ evm.substate = substate

variable {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-- The rule of an opcode, from the instruction that its byte runs on a frame of the code. -/
theorem At.rule {byte : UInt8} {op : Op}
    {run : Evm fork Nat → Except EvmError (Evm fork Nat)} {post : Evm fork Nat → Prop}
    (hlt : pc < code.size) (hbyte : code[pc] = byte) (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction fork op = some run)
    (h : ∀ evm, At code message pc stack memory gas state substate evm →
      ∃ after, run evm = .ok after ∧ post after) :
    Hoare fork (At code message pc stack memory gas state substate) post := by
  apply Triple.of_step
  intro evm hp
  obtain ⟨after, ok, hpost⟩ := h evm hp
  exact ⟨after,
    Step.of_code hp.2.2.2.2.2.2.2.1 hp.1 hp.2.2.2.1 hlt hbyte decoded hrun ok, hpost⟩

/-- The byte `0x5f + n`, for `n` from 1 to 32, decodes as PUSHn. -/
theorem decode_push (n : Fin 33) (hn : n.val ≠ 0) :
    Op.decode (0x5f + UInt8.ofNat n.val) = some (.push n) := by
  revert hn
  revert n
  decide

/-- PUSHn, for the `n` from 1 that the byte at the program counter decodes to.

It pushes the word of the `n` bytes after it, for 3 gas. -/
theorem push_of_decode {byte : UInt8} {n : Fin 33} {word : U256} (hlt : pc < code.size)
    (hbyte : code[pc] = byte) (decoded : Op.decode byte = some (.push n)) (hn : n.val ≠ 0)
    (hword : pushData code pc n = word) (hgas : 3 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate)
      (At code message (pc + (1 + n)) (word :: stack) memory (gas - 3) state substate) := by
  have hn' : n ≠ 0 := fun h => hn (by simp [h])
  apply At.rule hlt hbyte
    (ofByte_of_decode decoded (by simp [Op.since, hn', Fork.frontier_le])) (instruction_push n)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  have hlen : evm.stack.val.length < STACK_LIMIT := by rw [hst]; exact hstack
  rw [pushN_nat hn (by rw [hg]; exact hgas) hlen]
  refine ⟨_, rfl, hcode, hj, hm, by simp [hpc], by simp [hst, hcode, hpc, hword], hmem,
    by simp [hg, OPCODE_PUSH, VERY_LOW], hrun, herr, hout, hs, hss⟩

/-- PUSHn, for `n` from 1, pushes the word of the `n` bytes after it, for 3 gas. -/
theorem push {n : Fin 33} {word : U256} (hn : n.val ≠ 0) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x5f + UInt8.ofNat n.val)
    (decoded : Op.decode (0x5f + UInt8.ofNat n.val) = some (.push n))
    (hword : pushData code pc n = word) (hgas : 3 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate)
      (At code message (pc + (1 + n)) (word :: stack) memory (gas - 3) state substate) :=
  push_of_decode hlt hbyte decoded hn hword hgas hstack

/-- PUSH1 pushes the byte after it and costs 3, with room on the stack. -/
theorem push1 {byte : UInt8} (hlt : pc + 1 < code.size) (hop : code[pc]'(by omega) = 0x60)
    (hbyte : code[pc + 1] = byte) (hgas : 3 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate)
      (At code message (pc + 2) (BitVec.ofNat 256 byte.toNat :: stack) memory (gas - 3) state
        substate) :=
  push (n := 1) (by decide) (by omega) (by rw [hop]; decide) rfl
    (by simp [pushData, bufferRead, Base.byteAt, hlt, hbyte, Base.bytesToNat]) hgas hstack

end EthLib.Execution.Evm.Logic
