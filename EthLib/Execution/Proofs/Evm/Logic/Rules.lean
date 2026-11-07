module

public import EthLib.Execution.Proofs.Evm.Logic.Symbolic
public import EthLib.Execution.Proofs.Evm.Instructions.MemoryData
public import EthLib.Execution.Proofs.Evm.Instructions.ControlFlow
public import EthLib.Execution.Proofs.Evm.Instructions.Storage
public import EthLib.Execution.Proofs.Evm.Instructions.Return

/-!
# Proofs: rules for the opcodes of a contract that reads its call data and uses its storage

A contract that answers a call reads its call data, compares and jumps, and hashes memory.

It then reads and writes its storage, and returns a word.

The rule for SSTORE holds from Berlin to the fork before Glamsterdam, by EIP-2200 and EIP-2929.

Its price and its refund are those of the write, by EIP-2200 and EIP-3529.

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

/-- A triple whose postcondition holds of another memory, equal to the one it names. -/
theorem Hoare.memory_eq {P : Evm fork Nat → Prop} {code : ByteArray} {pc : Nat}
    {stack : List U256} {m m' : ByteArray} {gas : Nat} {st : State.TransactionState}
    {ss : Substate} (h : Hoare fork P (At code message pc stack m gas st ss)) (hm : m = m') :
    Hoare fork P (At code message pc stack m' gas st ss) := hm ▸ h

/-- A triple whose postcondition holds of another gas, equal to the one it names. -/
theorem Hoare.gas_eq {P : Evm fork Nat → Prop} {code : ByteArray} {pc : Nat}
    {stack : List U256} {m : ByteArray} {gas gas' : Nat} {st : State.TransactionState}
    {ss : Substate} (h : Hoare fork P (At code message pc stack m gas st ss))
    (hg : gas = gas') : Hoare fork P (At code message pc stack m gas' st ss) := hg ▸ h

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

/-- ISZERO runs the test for zero. -/
theorem instruction_iszero :
    instruction (Meter := Meter) fork .iszero = some (unaryOp OPCODE_ISZERO isZero) := by
  simp [instruction, stackOnlyStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- ADD runs the sum. -/
theorem instruction_add :
    instruction (Meter := Meter) fork .add = some (binaryOp OPCODE_ADD add) := by
  simp [instruction, stackOnlyStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- MLOAD runs the read of a word of memory. -/
theorem instruction_mload : instruction (Meter := Meter) fork .mload = some mloadStep := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, HOrElse.hOrElse,
    OrElse.orElse, Option.orElse]

/-- JUMP runs the jump. -/
theorem instruction_jump : instruction (Meter := Meter) fork .jump = some jumpStep := by
  simp [instruction, stackOnlyStep, controlFlowStep, HOrElse.hOrElse, OrElse.orElse,
    Option.orElse]

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

/-- A one-operand instruction of the stack, on `x`, puts `f x` in its place. -/
theorem unary {byte : UInt8} {op : Op} {cost : Nat} {f : U256 → U256} {x : U256}
    {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction (Meter := Nat) fork op = some (unaryOp cost f)) (hgas : cost ≤ gas) :
    Hoare fork (At code message pc (x :: rest) memory gas state substate)
      (At code message (pc + 1) (f x :: rest) memory (gas - cost) state substate) := by
  apply At.rule hlt hbyte decoded hrun
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  rw [unaryOp_cons hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem, by simp [hg], hrun, herr, hs, hss⟩

/-- JUMP to a JUMPDEST of the code goes there, for 8 gas. -/
theorem jump {destination : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x56) (hgas : 8 ≤ gas)
    (valid : isValidJumpDest (validJumpDestinations code) destination.toNat = true) :
    Hoare fork (At code message pc (destination :: rest) memory gas state substate)
      (At code message destination.toNat rest memory (gas - 8) state substate) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .jump) rfl (Fork.frontier_le _))
    instruction_jump
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  rw [jumpStep_of_isValidJumpDest hst (charge_nat (by rw [hg]; exact hgas))
    (by rw [hj]; exact valid)]
  exact ⟨_, rfl, hcode, hj, hm, rfl, rfl, hmem, by simp [hg, OPCODE_JUMP, MID], hrun, herr, hs,
    hss⟩

/-- MLOAD puts the word of memory at an offset in its place, after memory grows to hold it.

It pays 3 and the growth of memory. -/
theorem mload {start : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x51)
    (hgas : 3 + (extendMemory memory.size [(start, 32)]).cost ≤ gas) :
    Hoare fork (At code message pc (start :: rest) memory gas state substate)
      (At code message (pc + 1)
        (loadWord (memoryReadBytes
          (memoryExtend memory (extendMemory memory.size [(start, 32)]).expandBy)
          start.toNat 32) 0 32 :: rest)
        (memoryExtend memory (extendMemory memory.size [(start, 32)]).expandBy)
        (gas - (3 + (extendMemory memory.size [(start, 32)]).cost)) state substate) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .mload) rfl (Fork.frontier_le _))
    instruction_mload
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  subst hmem hg
  have hcost : OPCODE_MLOAD_BASE = 3 := rfl
  rw [mloadStep_cons hst]
  dsimp only
  rw [hcost, charge_nat hgas]
  refine ⟨_, rfl, hcode, hj, hm, by simp [hpc], ?_, ?_, ?_, hrun, herr, hs, hss⟩
  · show _ :: rest = _ :: rest
    rfl
  · simp
  · simp

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

/-! ## SSTORE -/

/-- SSTORE runs the write of a word of storage. -/
theorem instruction_sstore : instruction (Meter := Nat) fork .sstore = some sstoreStep := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, accountStep, storageStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- The step of SSTORE, from Berlin to before Glamsterdam, in a frame that may change the state.

It pops a key and a word, marks the slot of the current account accessed, and records its read.

It pays the price of the write, from the original, current and new words and the cold flag.

It writes the word, and adds the refund of the write to the refund counter. -/
theorem sstoreStep_eq (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {evm : Evm fork Nat} {key new : U256} {rest : List U256} {state' : State.TransactionState}
    (hst : evm.stack.val = key :: new :: rest) (hstatic : evm.message.isStatic = false)
    (hstipend : CALL_STIPEND < evm.gas)
    (hgas : sstoreCost fork
      (evm.state.getStorageOriginal evm.message.currentTarget (U256.toBeBytes key))
      (evm.state.getStorage evm.message.currentTarget (U256.toBeBytes key)) new
      (decide (U256.toBeBytes key ∉
        evm.substate.accessedStorageKeys.getD evm.message.currentTarget ∅)) ≤ evm.gas)
    (hset : (evm.state.recordStorageRead evm.message.currentTarget (U256.toBeBytes key)).setStorage
      evm.message.currentTarget (U256.toBeBytes key) new = .ok state') :
    ∃ after, sstoreStep evm = .ok after ∧
      after.code = evm.code ∧ after.validJumpDestinations = evm.validJumpDestinations ∧
      after.message = evm.message ∧ after.pc = evm.pc + 1 ∧ after.stack.val = rest ∧
      after.memory = evm.memory ∧
      after.gas = evm.gas - sstoreCost fork
        (evm.state.getStorageOriginal evm.message.currentTarget (U256.toBeBytes key))
        (evm.state.getStorage evm.message.currentTarget (U256.toBeBytes key)) new
        (decide (U256.toBeBytes key ∉
          evm.substate.accessedStorageKeys.getD evm.message.currentTarget ∅)) ∧
      after.running = evm.running ∧ after.error = evm.error ∧ after.state = state' ∧
      after.substate = { evm.substate with
        accessedStorageKeys := evm.substate.accessedStorageKeys.insert evm.message.currentTarget
          ((evm.substate.accessedStorageKeys.getD evm.message.currentTarget ∅).insert
            (U256.toBeBytes key))
        refundCounter := evm.substate.refundCounter + sstoreRefund fork
          (evm.state.getStorageOriginal evm.message.currentTarget (U256.toBeBytes key))
          (evm.state.getStorage evm.message.currentTarget (U256.toBeBytes key)) new } := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  have hist : Fork.istanbul ≤ fork := Nat.le_trans (by decide) hfork
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst hstatic hstipend hgas hset ⊢
  subst hst
  have hstate : sstoreStateGas fork (state.getStorageOriginal message.currentTarget
      (U256.toBeBytes key)) (state.getStorage message.currentTarget (U256.toBeBytes key)) new =
      0 := by simp [sstoreStateGas, hng]
  have hrefill : ∀ g : Nat, GasMeter.refill g (sstoreStateRefill fork
      (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
      (state.getStorage message.currentTarget (U256.toBeBytes key)) new) = g := fun _ => rfl
  have hgas' : sstoreCost fork
      (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
      (state.getStorage message.currentTarget (U256.toBeBytes key)) new
      (!decide (U256.toBeBytes key ∈ substate.accessedStorageKeys.getD message.currentTarget ∅))
      ≤ gas := by simpa using hgas
  simp [sstoreStep, hng, popWord, Stack.pop, bind, Except.bind, pure, Except.pure, hist,
    GasMeter.gasLeft, Nat.not_le.mpr hstipend, accessStorageKey, hfork, recordStorageRead,
    keepReads, refillStateGas, hrefill, chargeGas, GasMeter.charge, Nat.not_lt.mpr hgas',
    chargeStateGas, GasMeter.chargeState, hstate, hstatic, hset, Except.mapError, advance]

/-- From Berlin to before Glamsterdam, SSTORE writes a word to a slot of the current account.

The frame may change the state, and holds more than the stipend of 2300 gas, by EIP-2200.

The slot is cold when the transaction has not accessed it yet, by EIP-2929.

It pays the price of the write and adds its refund, from the original, current and new words.

The write needs the account of the current address, and gives the state `state'`. -/
theorem sstore (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {key new : U256}
    {rest : List U256} {cold : Bool} {state' : State.TransactionState}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x55) (hstatic : message.isStatic = false)
    (hcold : decide (U256.toBeBytes key ∉
      substate.accessedStorageKeys.getD message.currentTarget ∅) = cold)
    (hstipend : CALL_STIPEND < gas)
    (hgas : sstoreCost fork (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
      (state.getStorage message.currentTarget (U256.toBeBytes key)) new cold ≤ gas)
    (hset : (state.recordStorageRead message.currentTarget (U256.toBeBytes key)).setStorage
      message.currentTarget (U256.toBeBytes key) new = .ok state') :
    Hoare fork (At code message pc (key :: new :: rest) memory gas state substate)
      (At code message (pc + 1) rest memory
        (gas - sstoreCost fork
          (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
          (state.getStorage message.currentTarget (U256.toBeBytes key)) new cold)
        state'
        { substate with
          accessedStorageKeys := substate.accessedStorageKeys.insert message.currentTarget
            ((substate.accessedStorageKeys.getD message.currentTarget ∅).insert
              (U256.toBeBytes key))
          refundCounter := substate.refundCounter + sstoreRefund fork
            (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
            (state.getStorage message.currentTarget (U256.toBeBytes key)) new }) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .sstore) rfl (Fork.frontier_le _))
    instruction_sstore
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  subst hm hg hs hss hcold
  obtain ⟨after, h, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ :=
    sstoreStep_eq hfork hglam hst hstatic hstipend hgas hset
  exact ⟨after, h, by rw [a1, hcode], by rw [a2, hj], a3, by rw [a4, hpc], a5, by rw [a6, hmem],
    a7, by rw [a8, hrun], by rw [a9, herr], a10, a11⟩

end EthLib.Execution.Evm.Logic
