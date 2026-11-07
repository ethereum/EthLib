module

public import EthLib.Execution.Proofs.Evm.Logic.Symbolic
public import EthLib.Execution.Proofs.Evm.Instructions.MemoryData
public import EthLib.Execution.Proofs.Evm.Instructions.ControlFlow
public import EthLib.Execution.Proofs.Evm.Instructions.Storage
public import EthLib.Execution.Proofs.Evm.Instructions.Return

/-!
# Proofs: rules for the opcodes of a contract that reads its call data and its storage

A contract that answers a call reads its call data, compares and jumps, and hashes memory.

It then reads its storage, and returns a word.

Each rule here is a triple for one opcode, from one running frame of a code to the next.

The rules rest on the effect of each instruction on the stack, as its proofs state it.

They work out the charge of one counter of gas.

That is the meter of every fork before Glamsterdam.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork}

variable {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-! ## The instruction table -/

section Table

variable {Meter : Type} [GasMeter Meter]

/-- CALLDATALOAD runs the load of a word of the call data. -/
theorem instruction_calldataload :
    instruction (Meter := Meter) fork .calldataload = some calldataloadStep := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, HOrElse.hOrElse,
    OrElse.orElse, Option.orElse]

/-- SHR runs the right shift. -/
theorem instruction_shr :
    instruction (Meter := Meter) fork .shr = some (binaryOp OPCODE_SHR bitwiseShr) := by
  simp [instruction, stackOnlyStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- EQ runs the comparison for equality. -/
theorem instruction_eq :
    instruction (Meter := Meter) fork .eq = some (binaryOp OPCODE_EQ equal) := by
  simp [instruction, stackOnlyStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- DUP(n + 1) runs the copy of the word at depth `n`. -/
theorem instruction_dup (n : Fin 16) :
    instruction (Meter := Meter) fork (.dup n) = some (dupN n) := by
  simp [instruction, stackOnlyStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- KECCAK256 runs the hash of a range of memory. -/
theorem instruction_keccak256 :
    instruction (Meter := Meter) fork .keccak256 = some keccak256Step := by
  simp [instruction, stackOnlyStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- JUMPI runs the conditional jump. -/
theorem instruction_jumpi : instruction (Meter := Meter) fork .jumpi = some jumpiStep := by
  simp [instruction, stackOnlyStep, controlFlowStep, HOrElse.hOrElse, OrElse.orElse,
    Option.orElse]

/-- JUMPDEST runs the mark of a jump destination. -/
theorem instruction_jumpdest : instruction (Meter := Meter) fork .jumpdest = some jumpdestStep := by
  simp [instruction, stackOnlyStep, controlFlowStep, HOrElse.hOrElse, OrElse.orElse,
    Option.orElse]

/-- SLOAD runs the read of a slot of storage. -/
theorem instruction_sload : instruction (Meter := Meter) fork .sload = some sloadStep := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, accountStep, storageStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- From Byzantium, REVERT runs the halt with output and the revert error. -/
theorem instruction_revert (h : .byzantium ≤ fork) :
    instruction (Meter := Meter) fork .revert = some revertStep := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep, h,
    HOrElse.hOrElse, OrElse.orElse, Option.orElse]

end Table

/-- A charge that one counter of gas covers takes it from the counter. -/
theorem charge_nat {gas amount : Nat} (h : amount ≤ gas) :
    GasMeter.charge gas amount = .ok (gas - amount) := by
  simp [GasMeter.charge, Nat.not_lt.mpr h]

/-! ## The rules -/

/-- CALLDATALOAD on an offset puts the word of call data there in its place, for 3 gas. -/
theorem calldataload {start : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x35) (hgas : 3 ≤ gas) :
    Hoare fork (At code message pc (start :: rest) memory gas state substate)
      (At code message (pc + 1) (loadWord message.data start.toNat 32 :: rest) memory
        (gas - 3) state substate) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .calldataload) rfl (Fork.frontier_le _))
    instruction_calldataload
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  rw [calldataloadStep_cons hst, charge_nat (by rw [hg]; exact hgas)]
  refine ⟨_, rfl, hcode, hj, hm, by simp [hpc], by simp [hm], hmem,
    by simp [hg, OPCODE_CALLDATALOAD, VERY_LOW], hrun, herr, hs, hss⟩

/-- A two-operand instruction of the stack, on `x` then `y`, puts `f x y` in their place. -/
theorem binary {byte : UInt8} {op : Op} {cost : Nat} {f : U256 → U256 → U256} {x y : U256}
    {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction (Meter := Nat) fork op = some (binaryOp cost f)) (hgas : cost ≤ gas) :
    Hoare fork (At code message pc (x :: y :: rest) memory gas state substate)
      (At code message (pc + 1) (f x y :: rest) memory (gas - cost) state substate) := by
  apply At.rule hlt hbyte decoded hrun
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  rw [binaryOp_cons hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem, by simp [hg], hrun, herr, hs, hss⟩

/-- DUP1 pushes a copy of the top word, for 3 gas. -/
theorem dup1 {x : U256} {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0x80)
    (hgas : 3 ≤ gas) (hstack : (x :: rest).length < STACK_LIMIT) :
    Hoare fork (At code message pc (x :: rest) memory gas state substate)
      (At code message (pc + 1) (x :: x :: rest) memory (gas - 3) state substate) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .dup 0) rfl (Fork.frontier_le _))
    (instruction_dup 0)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  have hlen : evm.stack.val.length < STACK_LIMIT := by rw [hst]; exact hstack
  rw [dupN_of_getElem? (x := x) (by simp [hst]) hlen, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], by simp [hst], hmem,
    by simp [hg, OPCODE_DUP, VERY_LOW], hrun, herr, hs, hss⟩

/-- JUMPDEST costs 1 and goes on. -/
theorem jumpdest (hlt : pc < code.size) (hbyte : code[pc] = 0x5b) (hgas : 1 ≤ gas) :
    Hoare fork (At code message pc stack memory gas state substate)
      (At code message (pc + 1) stack memory (gas - 1) state substate) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .jumpdest) rfl (Fork.frontier_le _))
    instruction_jumpdest
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  rw [jumpdestStep_eq, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], hst, hmem, by simp [hg, OPCODE_JUMPDEST], hrun,
    herr, hs, hss⟩

/-- JUMPI on the condition 0 goes on to the next opcode, for 10 gas. -/
theorem jumpi_zero {destination : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x57) (hgas : 10 ≤ gas) :
    Hoare fork (At code message pc (destination :: 0 :: rest) memory gas state substate)
      (At code message (pc + 1) rest memory (gas - 10) state substate) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .jumpi) rfl (Fork.frontier_le _))
    instruction_jumpi
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  rw [jumpiStep_zero hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem, by simp [hg, OPCODE_JUMPI, HIGH],
    hrun, herr, hs, hss⟩

/-- JUMPI on a nonzero condition, to a JUMPDEST of the code, jumps there, for 10 gas. -/
theorem jumpi_taken {destination condition : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x57) (hgas : 10 ≤ gas) (nonzero : condition ≠ 0)
    (valid : isValidJumpDest (validJumpDestinations code) destination.toNat = true) :
    Hoare fork
      (At code message pc (destination :: condition :: rest) memory gas state substate)
      (At code message destination.toNat rest memory (gas - 10) state substate) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .jumpi) rfl (Fork.frontier_le _))
    instruction_jumpi
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  rw [jumpiStep_of_isValidJumpDest hst nonzero (charge_nat (by rw [hg]; exact hgas))
    (by rw [hj]; exact valid)]
  exact ⟨_, rfl, hcode, hj, hm, rfl, rfl, hmem, by simp [hg, OPCODE_JUMPI, HIGH], hrun, herr, hs,
    hss⟩

/-- MSTORE writes a word at an offset of memory, after memory grows to hold it.

It pays 3 and the growth of memory. -/
theorem mstore {start value : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x52)
    (hgas : 3 + (extendMemory memory.size [(start, 32)]).cost ≤ gas) :
    Hoare fork (At code message pc (start :: value :: rest) memory gas state substate)
      (At code message (pc + 1) rest
        (memoryWrite (memoryExtend memory (extendMemory memory.size [(start, 32)]).expandBy)
          start.toNat (wordBytes value))
        (gas - (3 + (extendMemory memory.size [(start, 32)]).cost)) state substate) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .mstore) rfl (Fork.frontier_le _))
    instruction_mstore
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  subst hmem hg
  have hcost : OPCODE_MSTORE_BASE = 3 := rfl
  rw [mstoreStep_cons hst]
  dsimp only
  rw [hcost, charge_nat hgas]
  refine ⟨_, rfl, hcode, hj, hm, by simp [hpc], ?_, ?_, ?_, hrun, herr, hs, hss⟩
  · show rest = rest
    rfl
  · simp
  · simp

/-- KECCAK256 puts the hash of a range of memory in place of its start and its size.

It pays 30, 6 for each word it hashes, and the growth of memory. -/
theorem keccak256 {start size : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x20)
    (hgas :
      30 + 6 * wordCount size.toNat + (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    Hoare fork (At code message pc (start :: size :: rest) memory gas state substate)
      (At code message (pc + 1)
        (keccak (memoryReadBytes
          (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat size.toNat) :: rest)
        (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
        (gas - (30 + 6 * wordCount size.toNat + (extendMemory memory.size [(start, size)]).cost))
        state substate) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .keccak256) rfl (Fork.frontier_le _))
    instruction_keccak256
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  subst hmem hg
  rw [keccak256Step_cons hst]
  dsimp only
  rw [charge_nat hgas]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, rfl, rfl, hrun, herr, hs, hss⟩

/-- The price of SLOAD from Berlin: 2100 for a cold slot and 100 for a warm one, by EIP-2929. -/
theorem sloadCost_of_berlin (h : .berlin ≤ fork) (cold : Bool) :
    sloadCost fork cold = if cold then 2100 else 100 := by
  simp [sloadCost, h, COLD_STORAGE_ACCESS, WARM_ACCESS]

/-- From Berlin, SLOAD puts the word of a slot of the current account in place of its key.

The slot is cold when the transaction has not accessed it yet.

It pays 2100 for a cold slot and 100 for a warm one, then records the slot as accessed and read. -/
theorem sload (hfork : .berlin ≤ fork) {key : U256} {rest : List U256} {cold : Bool}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x54)
    (hcold : decide (U256.toBeBytes key ∉
      substate.accessedStorageKeys.getD message.currentTarget ∅) = cold)
    (hgas : (if cold then 2100 else 100) ≤ gas) :
    Hoare fork (At code message pc (key :: rest) memory gas state substate)
      (At code message (pc + 1)
        (state.getStorage message.currentTarget (U256.toBeBytes key) :: rest) memory
        (gas - if cold then 2100 else 100)
        (state.recordStorageRead message.currentTarget (U256.toBeBytes key))
        { substate with
          accessedStorageKeys := (substate.accessedStorageKeys.insert message.currentTarget
            ((substate.accessedStorageKeys.getD message.currentTarget ∅).insert
              (U256.toBeBytes key))) }) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .sload) rfl (Fork.frontier_le _))
    instruction_sload
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  subst hm hg hs hss
  rw [sloadStep_cons hst]
  simp only [accessStorageKey, hfork, ↓reduceIte, hcold, sloadCost_of_berlin hfork]
  rw [charge_nat hgas]
  refine ⟨_, rfl, hcode, hj, rfl, by simp [hpc], ?_, hmem, ?_, hrun, herr, rfl, rfl⟩
  · show _ :: rest = _ :: rest
    rfl
  · simp

/-- What a stopped frame holds: whether it reverted, its output, its gas, state and substate. -/
def Halted (reverted : Bool) (output : ByteArray) (gas : Nat) (state : State.TransactionState)
    (substate : Substate) (evm : Evm fork Nat) : Prop :=
  evm.running = false ∧ evm.error = (if reverted then some .revert else none) ∧
    evm.output = output ∧ evm.gas = gas ∧ evm.state = state ∧ evm.substate = substate

/-- RETURN stops the frame with a range of memory as its output, and pays the growth of memory. -/
theorem «return» {start size : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0xf3) (hgas : (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    Spec fork (At code message pc (start :: size :: rest) memory gas state substate)
      (Halted false
        (memoryReadBytes (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat size.toNat)
        (gas - (extendMemory memory.size [(start, size)]).cost) state substate) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .«return») rfl (Fork.frontier_le _))
    instruction_return
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  subst hmem hg
  rw [returnStep_cons hst]
  dsimp only
  rw [charge_nat hgas]
  exact ⟨_, rfl, rfl, rfl, herr, rfl, by simp, hs, hss⟩

/-- From Byzantium, REVERT stops the frame with the revert error and a range of memory as output.

It pays the growth of memory, and keeps the gas left. -/
theorem revert (hfork : .byzantium ≤ fork) {start size : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xfd)
    (hgas : (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    Spec fork (At code message pc (start :: size :: rest) memory gas state substate)
      (Halted true
        (memoryReadBytes (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat size.toNat)
        (gas - (extendMemory memory.size [(start, size)]).cost) state substate) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .revert) rfl hfork)
    (instruction_revert hfork)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  subst hmem hg
  rw [revertStep_eq, returnStep_cons hst]
  dsimp only
  rw [charge_nat hgas]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, by simp, hs, hss⟩

end EthLib.Execution.Evm.Logic
