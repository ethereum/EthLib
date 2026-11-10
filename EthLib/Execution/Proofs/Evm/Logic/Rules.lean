module

public import EthLib.Execution.Proofs.Evm.Logic.NoAbort
public import EthLib.Execution.Proofs.Evm.Instructions.MemoryData
public import EthLib.Execution.Proofs.Evm.Instructions.ControlFlow
public import EthLib.Execution.Proofs.Evm.Instructions.Storage
public import EthLib.Execution.Proofs.Evm.Instructions.Return
public import EthLib.Execution.Proofs.Evm.Instructions.EnvironmentData
public import EthLib.Execution.Proofs.State.Tracker
public import EthLib.Execution.Proofs.Evm.Instructions.AccountData

/-!
# Proofs: rules for the opcodes of a contract that reads its call data and uses its storage

A contract that answers a call reads its call data and its caller, compares and jumps.

It also hashes memory.

It then reads and writes its storage, and returns a word.

The rule for SSTORE holds from Berlin, by EIP-2200 and EIP-2929.

Its price and its refund are those of EIP-2200, with the prices of EIP-2929.

From Glamsterdam, its one counter also pays the state gas of EIP-8037 and ignores its refill.

From London, the refund to clear a slot is that of EIP-3529.

Each rule here is a triple for one opcode, from one running frame of a code to the next.

Most rules here also hold over the steps from frames that are monotone in gas.

The rule over the steps of the logic then follows from that form.

If the instruction never aborts, its rule is first proved over steps that never abort with less gas.

The form over the steps from frames that are monotone in gas then follows from it.

SSTORE may abort, so its rule is first proved over the steps from frames that are monotone in gas.

GAS has no such form, since it pushes the gas left.

EXTCODESIZE, the stop past the end of the code and the write of SSTORE to an account have none yet.

The rules rest on the effect of each instruction on the stack, as its proofs state it.

They work out the charge of one counter of gas.

That is the meter of every fork before Glamsterdam.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256 Address Bytes32)
open GasCosts

variable {fork : Fork}

variable {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}
  {returnData : ByteArray}

/-- A triple whose postcondition holds of another memory, equal to the one it names. -/
theorem Hoare.memory_eq {P : Evm fork Nat → Prop} {code : ByteArray} {pc : Nat}
    {stack : List U256} {m m' : ByteArray} {gas : Nat} {st : State.TransactionState}
    {ss : Substate} (h : Hoare fork P (At code message pc stack m gas st ss returnData))
    (hm : m = m') :
    Hoare fork P (At code message pc stack m' gas st ss returnData) := hm ▸ h

/-- A triple whose postcondition holds of another gas, equal to the one it names. -/
theorem Hoare.gas_eq {P : Evm fork Nat → Prop} {code : ByteArray} {pc : Nat}
    {stack : List U256} {m : ByteArray} {gas gas' : Nat} {st : State.TransactionState}
    {ss : Substate} (h : Hoare fork P (At code message pc stack m gas st ss returnData))
    (hg : gas = gas') : Hoare fork P (At code message pc stack m gas' st ss returnData) := hg ▸ h

/-! ## The instruction table -/

section Table

variable {Meter : Type} [GasMeter Meter]

/-- CALLDATALOAD runs the load of a word of the call data. -/
theorem instruction_calldataload :
    instruction (Meter := Meter) fork .calldataload = some calldataloadStep := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, HOrElse.hOrElse,
    OrElse.orElse, Option.orElse]

/-- CALLER runs the read of the caller of the message. -/
theorem instruction_caller : instruction (Meter := Meter) fork .caller =
    some (readFrame OPCODE_CALLER fun evm => evm.message.caller.toU256) := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

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

/-- SUB runs the difference. -/
theorem instruction_sub :
    instruction (Meter := Meter) fork .sub = some (binaryOp OPCODE_SUB sub) := by
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

/-- PUSHn, for the `n` from 1 that the byte at the program counter decodes to.

It pushes the word of the `n` bytes after it, for 3 gas.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem push_of_decodeGA {byte : UInt8} {n : Fin 33} {word : U256} (hlt : pc < code.size)
    (hbyte : code[pc] = byte) (decoded : Op.decode byte = some (.push n)) (hn : n.val ≠ 0)
    (hword : pushData code pc n = word) (hgas : 3 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareGA fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + (1 + n)) (word :: stack) memory (gas - 3) state substate
        returnData) := by
  have hn' : n ≠ 0 := fun h => hn (by simp [h])
  apply At.ruleGA hlt hbyte
    (ofByte_of_decode decoded (by simp [Op.since, hn', Fork.frontier_le])) (instruction_push n)
    (runMono_pushN n) (noAbort_pushN n)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  have hlen : evm.stack.val.length < STACK_LIMIT := by rw [hst]; exact hstack
  rw [pushN_nat hn (by rw [hg]; exact hgas) hlen]
  refine ⟨_, rfl, hcode, hj, hm, by simp [hpc], by simp [hst, hcode, hpc, hword], hmem,
    by simp [hg, OPCODE_PUSH, VERY_LOW], hrun, herr, hout, hs, hss, hrd⟩

/-- PUSHn, for the `n` from 1 that the byte at the program counter decodes to.

It pushes the word of the `n` bytes after it, for 3 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem push_of_decodeG {byte : UInt8} {n : Fin 33} {word : U256} (hlt : pc < code.size)
    (hbyte : code[pc] = byte) (decoded : Op.decode byte = some (.push n)) (hn : n.val ≠ 0)
    (hword : pushData code pc n = word) (hgas : 3 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + (1 + n)) (word :: stack) memory (gas - 3) state substate
        returnData) :=
  (push_of_decodeGA hlt hbyte decoded hn hword hgas hstack).toG

/-- PUSHn, for the `n` from 1 that the byte at the program counter decodes to.

It pushes the word of the `n` bytes after it, for 3 gas. -/
theorem push_of_decode {byte : UInt8} {n : Fin 33} {word : U256} (hlt : pc < code.size)
    (hbyte : code[pc] = byte) (decoded : Op.decode byte = some (.push n)) (hn : n.val ≠ 0)
    (hword : pushData code pc n = word) (hgas : 3 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + (1 + n)) (word :: stack) memory (gas - 3) state substate
        returnData) :=
  (push_of_decodeG hlt hbyte decoded hn hword hgas hstack).toHoare

/-- PUSHn, for `n` from 1, pushes the word of the `n` bytes after it, for 3 gas.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem pushGA {n : Fin 33} {word : U256} (hn : n.val ≠ 0) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x5f + UInt8.ofNat n.val)
    (decoded : Op.decode (0x5f + UInt8.ofNat n.val) = some (.push n))
    (hword : pushData code pc n = word) (hgas : 3 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareGA fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + (1 + n)) (word :: stack) memory (gas - 3) state substate
        returnData) :=
  push_of_decodeGA hlt hbyte decoded hn hword hgas hstack

/-- PUSHn, for `n` from 1, pushes the word of the `n` bytes after it, for 3 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem pushG {n : Fin 33} {word : U256} (hn : n.val ≠ 0) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x5f + UInt8.ofNat n.val)
    (decoded : Op.decode (0x5f + UInt8.ofNat n.val) = some (.push n))
    (hword : pushData code pc n = word) (hgas : 3 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + (1 + n)) (word :: stack) memory (gas - 3) state substate
        returnData) :=
  (pushGA hn hlt hbyte decoded hword hgas hstack).toG

/-- PUSHn, for `n` from 1, pushes the word of the `n` bytes after it, for 3 gas. -/
theorem push {n : Fin 33} {word : U256} (hn : n.val ≠ 0) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x5f + UInt8.ofNat n.val)
    (decoded : Op.decode (0x5f + UInt8.ofNat n.val) = some (.push n))
    (hword : pushData code pc n = word) (hgas : 3 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + (1 + n)) (word :: stack) memory (gas - 3) state substate
        returnData) :=
  (pushG hn hlt hbyte decoded hword hgas hstack).toHoare

/-- PUSH1 pushes the byte after it and costs 3, with room on the stack.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem push1GA {byte : UInt8} (hlt : pc + 1 < code.size) (hop : code[pc]'(by omega) = 0x60)
    (hbyte : code[pc + 1] = byte) (hgas : 3 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareGA fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 2) (BitVec.ofNat 256 byte.toNat :: stack) memory (gas - 3) state
        substate returnData) :=
  pushGA (n := 1) (by decide) (by omega) (by rw [hop]; decide) rfl
    (by simp [pushData, bufferRead, Base.byteAt, hlt, hbyte, Base.bytesToNat]) hgas hstack

/-- PUSH1 pushes the byte after it and costs 3, with room on the stack.

It holds over the steps from frames that are monotone in gas. -/
theorem push1G {byte : UInt8} (hlt : pc + 1 < code.size) (hop : code[pc]'(by omega) = 0x60)
    (hbyte : code[pc + 1] = byte) (hgas : 3 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 2) (BitVec.ofNat 256 byte.toNat :: stack) memory (gas - 3) state
        substate returnData) :=
  (push1GA hlt hop hbyte hgas hstack).toG

/-- PUSH1 pushes the byte after it and costs 3, with room on the stack. -/
theorem push1 {byte : UInt8} (hlt : pc + 1 < code.size) (hop : code[pc]'(by omega) = 0x60)
    (hbyte : code[pc + 1] = byte) (hgas : 3 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 2) (BitVec.ofNat 256 byte.toNat :: stack) memory (gas - 3) state
        substate returnData) :=
  (push1G hlt hop hbyte hgas hstack).toHoare

/-- CALLDATALOAD on an offset puts the word of call data there in its place, for 3 gas.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem calldataloadGA {start : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x35) (hgas : 3 ≤ gas) :
    HoareGA fork (At code message pc (start :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (loadWord message.data start.toNat 32 :: rest) memory
        (gas - 3) state substate returnData) := by
  apply At.ruleGA hlt hbyte (ofByte_of_decode (op := .calldataload) rfl (Fork.frontier_le _))
    instruction_calldataload runMono_calldataload noAbort_calldataload
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [calldataloadStep_cons hst, charge_nat (by rw [hg]; exact hgas)]
  refine ⟨_, rfl, hcode, hj, hm, by simp [hpc], by simp [hm], hmem,
    by simp [hg, OPCODE_CALLDATALOAD, VERY_LOW], hrun, herr, hout, hs, hss, hrd⟩

/-- CALLDATALOAD on an offset puts the word of call data there in its place, for 3 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem calldataloadG {start : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x35) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (start :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (loadWord message.data start.toNat 32 :: rest) memory
        (gas - 3) state substate returnData) :=
  (calldataloadGA hlt hbyte hgas).toG

/-- CALLDATALOAD on an offset puts the word of call data there in its place, for 3 gas. -/
theorem calldataload {start : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x35) (hgas : 3 ≤ gas) :
    Hoare fork (At code message pc (start :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (loadWord message.data start.toNat 32 :: rest) memory
        (gas - 3) state substate returnData) :=
  (calldataloadG hlt hbyte hgas).toHoare

/-- An opcode whose instruction reads the frame pushes the word it reads, and pays its price.

The read must give `word` on every frame with the code, the message, the counter and the memory.

The stack needs room for one more word.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem push_of_readFrameGA {byte : UInt8} {op : Op} {cost : Nat} {f : Evm fork Nat → U256}
    {word : U256} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction (Meter := Nat) fork op = some (readFrame cost f))
    (hword : ∀ evm : Evm fork Nat, evm.code = code → evm.message = message → evm.pc = pc →
      evm.memory = memory → f evm = word)
    (hgas : cost ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareGA fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (word :: stack) memory (gas - cost) state substate returnData) := by
  apply At.ruleGA_of_follows (never := noAbort_readFrame _ _) hlt hbyte decoded hrun
  · rintro _ ⟨hcode, -, hm, hpc, -, hmem, -⟩ k low rfl
    exact follows_readFrame cost f fun g =>
      (hword { low with gas := g } hcode hm hpc hmem).trans (hword low hcode hm hpc hmem).symm
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [readFrame_of_length_lt (by rw [hst]; exact hstack), charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], by
      dsimp only
      rw [hword { evm with gas := evm.gas - cost } hcode hm hpc hmem, hst], hmem,
    by simp [hg], hrun, herr, hout, hs, hss, hrd⟩

/-- An opcode whose instruction reads the frame pushes the word it reads, and pays its price.

The read must give `word` on every frame with the code, the message, the counter and the memory.

The stack needs room for one more word.

It holds over the steps from frames that are monotone in gas. -/
theorem push_of_readFrameG {byte : UInt8} {op : Op} {cost : Nat} {f : Evm fork Nat → U256}
    {word : U256} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction (Meter := Nat) fork op = some (readFrame cost f))
    (hword : ∀ evm : Evm fork Nat, evm.code = code → evm.message = message → evm.pc = pc →
      evm.memory = memory → f evm = word)
    (hgas : cost ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (word :: stack) memory (gas - cost) state substate returnData) :=
  (push_of_readFrameGA hlt hbyte decoded hrun hword hgas hstack).toG

/-- An opcode whose instruction reads the frame pushes the word it reads, and pays its price.

The read must give `word` on every frame with the code, the message, the counter and the memory.

The stack needs room for one more word. -/
theorem push_of_readFrame {byte : UInt8} {op : Op} {cost : Nat} {f : Evm fork Nat → U256}
    {word : U256} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction (Meter := Nat) fork op = some (readFrame cost f))
    (hword : ∀ evm : Evm fork Nat, evm.code = code → evm.message = message → evm.pc = pc →
      evm.memory = memory → f evm = word)
    (hgas : cost ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (word :: stack) memory (gas - cost) state substate returnData) :=
  (push_of_readFrameG hlt hbyte decoded hrun hword hgas hstack).toHoare

/-- CALLER pushes the address of the caller of the message as a word, for 2 gas.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem callerGA (hlt : pc < code.size) (hbyte : code[pc] = 0x33) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareGA fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (message.caller.toU256 :: stack) memory (gas - 2) state
        substate returnData) :=
  push_of_readFrameGA hlt hbyte (ofByte_of_decode (op := .caller) rfl (Fork.frontier_le _))
    instruction_caller (fun _ _ hm _ _ => by rw [hm]) hgas hstack

/-- CALLER pushes the address of the caller of the message as a word, for 2 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem callerG (hlt : pc < code.size) (hbyte : code[pc] = 0x33) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (message.caller.toU256 :: stack) memory (gas - 2) state
        substate returnData) :=
  (callerGA hlt hbyte hgas hstack).toG

/-- CALLER pushes the address of the caller of the message as a word, for 2 gas. -/
theorem caller (hlt : pc < code.size) (hbyte : code[pc] = 0x33) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (message.caller.toU256 :: stack) memory (gas - 2) state
        substate returnData) :=
  (callerG hlt hbyte hgas hstack).toHoare

/-- CALLVALUE pushes the value that the message sends, for 2 gas.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem callvalueGA (hlt : pc < code.size) (hbyte : code[pc] = 0x34) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareGA fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (message.value :: stack) memory (gas - 2) state substate
        returnData) :=
  push_of_readFrameGA hlt hbyte (ofByte_of_decode (op := .callvalue) rfl (Fork.frontier_le _))
    rfl (fun _ _ hm _ _ => by rw [hm]) hgas hstack

/-- CALLVALUE pushes the value that the message sends, for 2 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem callvalueG (hlt : pc < code.size) (hbyte : code[pc] = 0x34) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (message.value :: stack) memory (gas - 2) state substate
        returnData) :=
  (callvalueGA hlt hbyte hgas hstack).toG

/-- CALLVALUE pushes the value that the message sends, for 2 gas. -/
theorem callvalue (hlt : pc < code.size) (hbyte : code[pc] = 0x34) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (message.value :: stack) memory (gas - 2) state substate
        returnData) :=
  (callvalueG hlt hbyte hgas hstack).toHoare

/-- ADDRESS pushes the address of the current account as a word, for 2 gas.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem addressGA (hlt : pc < code.size) (hbyte : code[pc] = 0x30) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareGA fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (message.currentTarget.toU256 :: stack) memory (gas - 2) state
        substate returnData) :=
  push_of_readFrameGA hlt hbyte (ofByte_of_decode (op := .address) rfl (Fork.frontier_le _))
    rfl (fun _ _ hm _ _ => by rw [hm]) hgas hstack

/-- ADDRESS pushes the address of the current account as a word, for 2 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem addressG (hlt : pc < code.size) (hbyte : code[pc] = 0x30) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (message.currentTarget.toU256 :: stack) memory (gas - 2) state
        substate returnData) :=
  (addressGA hlt hbyte hgas hstack).toG

/-- ADDRESS pushes the address of the current account as a word, for 2 gas. -/
theorem address (hlt : pc < code.size) (hbyte : code[pc] = 0x30) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (message.currentTarget.toU256 :: stack) memory (gas - 2) state
        substate returnData) :=
  (addressG hlt hbyte hgas hstack).toHoare

/-- ORIGIN pushes the address of the sender of the transaction as a word, for 2 gas.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem originGA (hlt : pc < code.size) (hbyte : code[pc] = 0x32) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareGA fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (message.txEnv.origin.toU256 :: stack) memory (gas - 2) state
        substate returnData) :=
  push_of_readFrameGA hlt hbyte (ofByte_of_decode (op := .origin) rfl (Fork.frontier_le _))
    rfl (fun _ _ hm _ _ => by rw [hm]) hgas hstack

/-- ORIGIN pushes the address of the sender of the transaction as a word, for 2 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem originG (hlt : pc < code.size) (hbyte : code[pc] = 0x32) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (message.txEnv.origin.toU256 :: stack) memory (gas - 2) state
        substate returnData) :=
  (originGA hlt hbyte hgas hstack).toG

/-- ORIGIN pushes the address of the sender of the transaction as a word, for 2 gas. -/
theorem origin (hlt : pc < code.size) (hbyte : code[pc] = 0x32) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (message.txEnv.origin.toU256 :: stack) memory (gas - 2) state
        substate returnData) :=
  (originG hlt hbyte hgas hstack).toHoare

/-- CALLDATASIZE pushes the size of the call data, for 2 gas.

The word is the size modulo `2 ^ 256`.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem calldatasizeGA (hlt : pc < code.size) (hbyte : code[pc] = 0x36) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareGA fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 message.data.size :: stack) memory (gas - 2)
        state substate returnData) :=
  push_of_readFrameGA hlt hbyte (ofByte_of_decode (op := .calldatasize) rfl (Fork.frontier_le _))
    rfl (fun _ _ hm _ _ => by rw [hm]) hgas hstack

/-- CALLDATASIZE pushes the size of the call data, for 2 gas.

The word is the size modulo `2 ^ 256`.

It holds over the steps from frames that are monotone in gas. -/
theorem calldatasizeG (hlt : pc < code.size) (hbyte : code[pc] = 0x36) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 message.data.size :: stack) memory (gas - 2)
        state substate returnData) :=
  (calldatasizeGA hlt hbyte hgas hstack).toG

/-- CALLDATASIZE pushes the size of the call data, for 2 gas.

The word is the size modulo `2 ^ 256`. -/
theorem calldatasize (hlt : pc < code.size) (hbyte : code[pc] = 0x36) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 message.data.size :: stack) memory (gas - 2)
        state substate returnData) :=
  (calldatasizeG hlt hbyte hgas hstack).toHoare

/-- CODESIZE pushes the size of the code, for 2 gas.

The word is the size modulo `2 ^ 256`.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem codesizeGA (hlt : pc < code.size) (hbyte : code[pc] = 0x38) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareGA fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 code.size :: stack) memory (gas - 2) state
        substate returnData) :=
  push_of_readFrameGA hlt hbyte (ofByte_of_decode (op := .codesize) rfl (Fork.frontier_le _))
    rfl (fun _ hc _ _ _ => by rw [hc]) hgas hstack

/-- CODESIZE pushes the size of the code, for 2 gas.

The word is the size modulo `2 ^ 256`.

It holds over the steps from frames that are monotone in gas. -/
theorem codesizeG (hlt : pc < code.size) (hbyte : code[pc] = 0x38) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 code.size :: stack) memory (gas - 2) state
        substate returnData) :=
  (codesizeGA hlt hbyte hgas hstack).toG

/-- CODESIZE pushes the size of the code, for 2 gas.

The word is the size modulo `2 ^ 256`. -/
theorem codesize (hlt : pc < code.size) (hbyte : code[pc] = 0x38) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 code.size :: stack) memory (gas - 2) state
        substate returnData) :=
  (codesizeG hlt hbyte hgas hstack).toHoare

/-- PC pushes the program counter of the opcode, for 2 gas.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem pc_ruleGA (hlt : pc < code.size) (hbyte : code[pc] = 0x58) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareGA fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 pc :: stack) memory (gas - 2) state
        substate returnData) :=
  push_of_readFrameGA hlt hbyte (ofByte_of_decode (op := .pc) rfl (Fork.frontier_le _))
    rfl (fun _ _ _ hp _ => by rw [hp]) hgas hstack

/-- PC pushes the program counter of the opcode, for 2 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem pc_ruleG (hlt : pc < code.size) (hbyte : code[pc] = 0x58) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 pc :: stack) memory (gas - 2) state
        substate returnData) :=
  (pc_ruleGA hlt hbyte hgas hstack).toG

/-- PC pushes the program counter of the opcode, for 2 gas. -/
theorem pc_rule (hlt : pc < code.size) (hbyte : code[pc] = 0x58) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 pc :: stack) memory (gas - 2) state
        substate returnData) :=
  (pc_ruleG hlt hbyte hgas hstack).toHoare

/-- MSIZE pushes the size of the memory, for 2 gas.

The word is the size modulo `2 ^ 256`.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem msizeGA (hlt : pc < code.size) (hbyte : code[pc] = 0x59) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareGA fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 memory.size :: stack) memory (gas - 2) state
        substate returnData) :=
  push_of_readFrameGA hlt hbyte (ofByte_of_decode (op := .msize) rfl (Fork.frontier_le _))
    rfl (fun _ _ _ _ hmem => by rw [hmem]) hgas hstack

/-- MSIZE pushes the size of the memory, for 2 gas.

The word is the size modulo `2 ^ 256`.

It holds over the steps from frames that are monotone in gas. -/
theorem msizeG (hlt : pc < code.size) (hbyte : code[pc] = 0x59) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 memory.size :: stack) memory (gas - 2) state
        substate returnData) :=
  (msizeGA hlt hbyte hgas hstack).toG

/-- MSIZE pushes the size of the memory, for 2 gas.

The word is the size modulo `2 ^ 256`. -/
theorem msize (hlt : pc < code.size) (hbyte : code[pc] = 0x59) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 memory.size :: stack) memory (gas - 2) state
        substate returnData) :=
  (msizeG hlt hbyte hgas hstack).toHoare

/-- From Byzantium, RETURNDATASIZE pushes the size of the return data, for 2 gas, by EIP-211.

The frame keeps its return data.

The word is the size modulo `2 ^ 256`.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem returndatasizeGA (hfork : .byzantium ≤ fork) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x3d) (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareGA fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 returnData.size :: stack) memory (gas - 2)
        state substate returnData) := by
  apply At.ruleGA_of_follows (never := noAbort_readFrame _ _)
    (run := readFrame OPCODE_RETURNDATASIZE fun evm => BitVec.ofNat 256 evm.returnData.size)
    hlt hbyte
    (ofByte_of_decode (op := .returndatasize) rfl hfork) rfl
  · rintro _ - k low rfl
    exact follows_readFrame _ _ fun _ => rfl
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  have ok := readFrame_of_length_lt (cost := OPCODE_RETURNDATASIZE)
    (value := fun evm => BitVec.ofNat 256 evm.returnData.size) (by rw [hst]; exact hstack)
  have hcost : OPCODE_RETURNDATASIZE = 2 := rfl
  rw [hcost, hg, charge_nat hgas] at ok
  exact ⟨_, ok, hcode, hj, hm, by simp [hpc], by simp [hst, hrd], hmem, rfl, hrun, herr, hout, hs,
    hss, hrd⟩

/-- From Byzantium, RETURNDATASIZE pushes the size of the return data, for 2 gas, by EIP-211.

The frame keeps its return data.

The word is the size modulo `2 ^ 256`.

It holds over the steps from frames that are monotone in gas. -/
theorem returndatasizeG (hfork : .byzantium ≤ fork) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x3d) (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 returnData.size :: stack) memory (gas - 2)
        state substate returnData) :=
  (returndatasizeGA hfork hlt hbyte hgas hstack).toG

/-- From Byzantium, RETURNDATASIZE pushes the size of the return data, for 2 gas, by EIP-211.

The frame keeps its return data.

The word is the size modulo `2 ^ 256`. -/
theorem returndatasize (hfork : .byzantium ≤ fork) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x3d) (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 returnData.size :: stack) memory (gas - 2)
        state substate returnData) :=
  (returndatasizeG hfork hlt hbyte hgas hstack).toHoare

/-- A two-operand instruction of the stack, on `x` then `y`, puts `f x y` in their place.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem binaryGA {byte : UInt8} {op : Op} {cost : Nat} {f : U256 → U256 → U256} {x y : U256}
    {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction (Meter := Nat) fork op = some (binaryOp cost f)) (hgas : cost ≤ gas) :
    HoareGA fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (f x y :: rest) memory (gas - cost) state substate returnData) := by
  apply At.ruleGA hlt hbyte decoded hrun (runMono_binaryOp cost f) (noAbort_binaryOp cost f)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [binaryOp_cons hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem, by simp [hg], hrun, herr, hout, hs, hss,
    hrd⟩

/-- A two-operand instruction of the stack, on `x` then `y`, puts `f x y` in their place.

It holds over the steps from frames that are monotone in gas. -/
theorem binaryG {byte : UInt8} {op : Op} {cost : Nat} {f : U256 → U256 → U256} {x y : U256}
    {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction (Meter := Nat) fork op = some (binaryOp cost f)) (hgas : cost ≤ gas) :
    HoareG fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (f x y :: rest) memory (gas - cost) state substate returnData) :=
  (binaryGA hlt hbyte decoded hrun hgas).toG

/-- A two-operand instruction of the stack, on `x` then `y`, puts `f x y` in their place. -/
theorem binary {byte : UInt8} {op : Op} {cost : Nat} {f : U256 → U256 → U256} {x y : U256}
    {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction (Meter := Nat) fork op = some (binaryOp cost f)) (hgas : cost ≤ gas) :
    Hoare fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (f x y :: rest) memory (gas - cost) state substate returnData) :=
  (binaryG hlt hbyte decoded hrun hgas).toHoare

/-- A one-operand instruction of the stack, on `x`, puts `f x` in its place.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem unaryGA {byte : UInt8} {op : Op} {cost : Nat} {f : U256 → U256} {x : U256}
    {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction (Meter := Nat) fork op = some (unaryOp cost f)) (hgas : cost ≤ gas) :
    HoareGA fork (At code message pc (x :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (f x :: rest) memory (gas - cost) state substate returnData) := by
  apply At.ruleGA hlt hbyte decoded hrun (runMono_unaryOp cost f) (noAbort_unaryOp cost f)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [unaryOp_cons hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem, by simp [hg], hrun, herr, hout, hs, hss,
    hrd⟩

/-- A one-operand instruction of the stack, on `x`, puts `f x` in its place.

It holds over the steps from frames that are monotone in gas. -/
theorem unaryG {byte : UInt8} {op : Op} {cost : Nat} {f : U256 → U256} {x : U256}
    {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction (Meter := Nat) fork op = some (unaryOp cost f)) (hgas : cost ≤ gas) :
    HoareG fork (At code message pc (x :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (f x :: rest) memory (gas - cost) state substate returnData) :=
  (unaryGA hlt hbyte decoded hrun hgas).toG

/-- A one-operand instruction of the stack, on `x`, puts `f x` in its place. -/
theorem unary {byte : UInt8} {op : Op} {cost : Nat} {f : U256 → U256} {x : U256}
    {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction (Meter := Nat) fork op = some (unaryOp cost f)) (hgas : cost ≤ gas) :
    Hoare fork (At code message pc (x :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (f x :: rest) memory (gas - cost) state substate returnData) :=
  (unaryG hlt hbyte decoded hrun hgas).toHoare

/-- JUMP to a JUMPDEST of the code goes there, for 8 gas.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem jumpGA {destination : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x56) (hgas : 8 ≤ gas)
    (valid : isValidJumpDest (validJumpDestinations code) destination.toNat = true) :
    HoareGA fork (At code message pc (destination :: rest) memory gas state substate returnData)
      (At code message destination.toNat rest memory (gas - 8) state substate returnData) := by
  apply At.ruleGA hlt hbyte (ofByte_of_decode (op := .jump) rfl (Fork.frontier_le _))
    instruction_jump runMono_jump noAbort_jump
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [jumpStep_of_isValidJumpDest hst (charge_nat (by rw [hg]; exact hgas))
    (by rw [hj]; exact valid)]
  exact ⟨_, rfl, hcode, hj, hm, rfl, rfl, hmem, by simp [hg, OPCODE_JUMP, MID], hrun, herr, hout,
    hs, hss, hrd⟩

/-- JUMP to a JUMPDEST of the code goes there, for 8 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem jumpG {destination : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x56) (hgas : 8 ≤ gas)
    (valid : isValidJumpDest (validJumpDestinations code) destination.toNat = true) :
    HoareG fork (At code message pc (destination :: rest) memory gas state substate returnData)
      (At code message destination.toNat rest memory (gas - 8) state substate returnData) :=
  (jumpGA hlt hbyte hgas valid).toG

/-- JUMP to a JUMPDEST of the code goes there, for 8 gas. -/
theorem jump {destination : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x56) (hgas : 8 ≤ gas)
    (valid : isValidJumpDest (validJumpDestinations code) destination.toNat = true) :
    Hoare fork (At code message pc (destination :: rest) memory gas state substate returnData)
      (At code message destination.toNat rest memory (gas - 8) state substate returnData) :=
  (jumpG hlt hbyte hgas valid).toHoare

/-- MLOAD puts the word of memory at an offset in its place, after memory grows to hold it.

It pays 3 and the growth of memory.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem mloadGA {start : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x51)
    (hgas : 3 + (extendMemory memory.size [(start, 32)]).cost ≤ gas) :
    HoareGA fork (At code message pc (start :: rest) memory gas state substate returnData)
      (At code message (pc + 1)
        (loadWord (memoryReadBytes
          (memoryExtend memory (extendMemory memory.size [(start, 32)]).expandBy)
          start.toNat 32) 0 32 :: rest)
        (memoryExtend memory (extendMemory memory.size [(start, 32)]).expandBy)
        (gas - (3 + (extendMemory memory.size [(start, 32)]).cost)) state substate returnData) := by
  apply At.ruleGA hlt hbyte (ofByte_of_decode (op := .mload) rfl (Fork.frontier_le _))
    instruction_mload runMono_mload noAbort_mload
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  subst hmem hg
  have hcost : OPCODE_MLOAD_BASE = 3 := rfl
  rw [mloadStep_cons hst]
  dsimp only
  rw [hcost, charge_nat hgas]
  refine ⟨_, rfl, hcode, hj, hm, by simp [hpc], ?_, ?_, ?_, hrun, herr, hout, hs, hss, hrd⟩
  · show _ :: rest = _ :: rest
    rfl
  · simp
  · simp

/-- MLOAD puts the word of memory at an offset in its place, after memory grows to hold it.

It pays 3 and the growth of memory.

It holds over the steps from frames that are monotone in gas. -/
theorem mloadG {start : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x51)
    (hgas : 3 + (extendMemory memory.size [(start, 32)]).cost ≤ gas) :
    HoareG fork (At code message pc (start :: rest) memory gas state substate returnData)
      (At code message (pc + 1)
        (loadWord (memoryReadBytes
          (memoryExtend memory (extendMemory memory.size [(start, 32)]).expandBy)
          start.toNat 32) 0 32 :: rest)
        (memoryExtend memory (extendMemory memory.size [(start, 32)]).expandBy)
        (gas - (3 + (extendMemory memory.size [(start, 32)]).cost)) state substate returnData) :=
  (mloadGA hlt hbyte hgas).toG

/-- MLOAD puts the word of memory at an offset in its place, after memory grows to hold it.

It pays 3 and the growth of memory. -/
theorem mload {start : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x51)
    (hgas : 3 + (extendMemory memory.size [(start, 32)]).cost ≤ gas) :
    Hoare fork (At code message pc (start :: rest) memory gas state substate returnData)
      (At code message (pc + 1)
        (loadWord (memoryReadBytes
          (memoryExtend memory (extendMemory memory.size [(start, 32)]).expandBy)
          start.toNat 32) 0 32 :: rest)
        (memoryExtend memory (extendMemory memory.size [(start, 32)]).expandBy)
        (gas - (3 + (extendMemory memory.size [(start, 32)]).cost)) state substate returnData) :=
  (mloadG hlt hbyte hgas).toHoare

/-- The byte `0x80 + n` decodes as DUP(n + 1). -/
theorem decode_dup (n : Fin 16) : Op.decode (0x80 + n.val).toUInt8 = some (.dup n) := by
  revert n
  decide

/-- DUP(n + 1), for the `n` that the byte at the program counter decodes to.

It pushes a copy of the word `x` at depth `n`, for 3 gas, with room for a word.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem dup_of_decodeGA {byte : UInt8} {n : Fin 16} {x : U256} (hlt : pc < code.size)
    (hbyte : code[pc] = byte) (decoded : Op.decode byte = some (.dup n))
    (hx : stack[n.val]? = some x) (hgas : 3 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareGA fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (x :: stack) memory (gas - 3) state substate returnData) := by
  apply At.ruleGA hlt hbyte (ofByte_of_decode decoded (Fork.frontier_le _)) (instruction_dup n)
    (runMono_dupN n) (noAbort_dupN n)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  have hlen : evm.stack.val.length < STACK_LIMIT := by rw [hst]; exact hstack
  rw [dupN_of_getElem? (x := x) (by rw [hst]; exact hx) hlen,
    charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], by simp [hst], hmem,
    by simp [hg, OPCODE_DUP, VERY_LOW], hrun, herr, hout, hs, hss, hrd⟩

/-- DUP(n + 1), for the `n` that the byte at the program counter decodes to.

It pushes a copy of the word `x` at depth `n`, for 3 gas, with room for a word.

It holds over the steps from frames that are monotone in gas. -/
theorem dup_of_decodeG {byte : UInt8} {n : Fin 16} {x : U256} (hlt : pc < code.size)
    (hbyte : code[pc] = byte) (decoded : Op.decode byte = some (.dup n))
    (hx : stack[n.val]? = some x) (hgas : 3 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (x :: stack) memory (gas - 3) state substate returnData) :=
  (dup_of_decodeGA hlt hbyte decoded hx hgas hstack).toG

/-- DUP(n + 1), for the `n` that the byte at the program counter decodes to.

It pushes a copy of the word `x` at depth `n`, for 3 gas, with room for a word. -/
theorem dup_of_decode {byte : UInt8} {n : Fin 16} {x : U256} (hlt : pc < code.size)
    (hbyte : code[pc] = byte) (decoded : Op.decode byte = some (.dup n))
    (hx : stack[n.val]? = some x) (hgas : 3 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (x :: stack) memory (gas - 3) state substate returnData) :=
  (dup_of_decodeG hlt hbyte decoded hx hgas hstack).toHoare

/-- DUP(n + 1) pushes a copy of the word `x` at depth `n`, for 3 gas, with room for a word.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem dupGA (n : Fin 16) {x : U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x80 + n.val).toUInt8) (hx : stack[n.val]? = some x) (hgas : 3 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareGA fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (x :: stack) memory (gas - 3) state substate returnData) :=
  dup_of_decodeGA hlt hbyte (decode_dup n) hx hgas hstack

/-- DUP(n + 1) pushes a copy of the word `x` at depth `n`, for 3 gas, with room for a word.

It holds over the steps from frames that are monotone in gas. -/
theorem dupG (n : Fin 16) {x : U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x80 + n.val).toUInt8) (hx : stack[n.val]? = some x) (hgas : 3 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (x :: stack) memory (gas - 3) state substate returnData) :=
  (dupGA n hlt hbyte hx hgas hstack).toG

/-- DUP(n + 1) pushes a copy of the word `x` at depth `n`, for 3 gas, with room for a word. -/
theorem dup (n : Fin 16) {x : U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x80 + n.val).toUInt8) (hx : stack[n.val]? = some x) (hgas : 3 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (x :: stack) memory (gas - 3) state substate returnData) :=
  (dupG n hlt hbyte hx hgas hstack).toHoare

/-- DUP1 pushes a copy of the top word, for 3 gas.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem dup1GA {x : U256} {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0x80)
    (hgas : 3 ≤ gas) (hstack : (x :: rest).length < STACK_LIMIT) :
    HoareGA fork (At code message pc (x :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (x :: x :: rest) memory (gas - 3) state substate returnData) :=
  dupGA 0 hlt (by rw [hbyte]; rfl) rfl hgas hstack

/-- DUP1 pushes a copy of the top word, for 3 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem dup1G {x : U256} {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0x80)
    (hgas : 3 ≤ gas) (hstack : (x :: rest).length < STACK_LIMIT) :
    HoareG fork (At code message pc (x :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (x :: x :: rest) memory (gas - 3) state substate returnData) :=
  (dup1GA hlt hbyte hgas hstack).toG

/-- DUP1 pushes a copy of the top word, for 3 gas. -/
theorem dup1 {x : U256} {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0x80)
    (hgas : 3 ≤ gas) (hstack : (x :: rest).length < STACK_LIMIT) :
    Hoare fork (At code message pc (x :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (x :: x :: rest) memory (gas - 3) state substate returnData) :=
  (dup1G hlt hbyte hgas hstack).toHoare

/-- JUMPDEST costs 1 and goes on.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem jumpdestGA (hlt : pc < code.size) (hbyte : code[pc] = 0x5b) (hgas : 1 ≤ gas) :
    HoareGA fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) stack memory (gas - 1) state substate returnData) := by
  apply At.ruleGA hlt hbyte (ofByte_of_decode (op := .jumpdest) rfl (Fork.frontier_le _))
    instruction_jumpdest runMono_jumpdest noAbort_jumpdest
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [jumpdestStep_eq, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], hst, hmem, by simp [hg, OPCODE_JUMPDEST], hrun,
    herr, hout, hs, hss, hrd⟩

/-- JUMPDEST costs 1 and goes on.

It holds over the steps from frames that are monotone in gas. -/
theorem jumpdestG (hlt : pc < code.size) (hbyte : code[pc] = 0x5b) (hgas : 1 ≤ gas) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) stack memory (gas - 1) state substate returnData) :=
  (jumpdestGA hlt hbyte hgas).toG

/-- JUMPDEST costs 1 and goes on. -/
theorem jumpdest (hlt : pc < code.size) (hbyte : code[pc] = 0x5b) (hgas : 1 ≤ gas) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) stack memory (gas - 1) state substate returnData) :=
  (jumpdestG hlt hbyte hgas).toHoare

/-- JUMPI on the condition 0 goes on to the next opcode, for 10 gas.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem jumpi_zeroGA {destination : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x57) (hgas : 10 ≤ gas) :
    HoareGA fork
      (At code message pc (destination :: 0 :: rest) memory gas state substate returnData)
      (At code message (pc + 1) rest memory (gas - 10) state substate returnData) := by
  apply At.ruleGA hlt hbyte (ofByte_of_decode (op := .jumpi) rfl (Fork.frontier_le _))
    instruction_jumpi runMono_jumpi noAbort_jumpi
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [jumpiStep_zero hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem, by simp [hg, OPCODE_JUMPI, HIGH],
    hrun, herr, hout, hs, hss, hrd⟩

/-- JUMPI on the condition 0 goes on to the next opcode, for 10 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem jumpi_zeroG {destination : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x57) (hgas : 10 ≤ gas) :
    HoareG fork (At code message pc (destination :: 0 :: rest) memory gas state substate returnData)
      (At code message (pc + 1) rest memory (gas - 10) state substate returnData) :=
  (jumpi_zeroGA hlt hbyte hgas).toG

/-- JUMPI on the condition 0 goes on to the next opcode, for 10 gas. -/
theorem jumpi_zero {destination : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x57) (hgas : 10 ≤ gas) :
    Hoare fork (At code message pc (destination :: 0 :: rest) memory gas state substate returnData)
      (At code message (pc + 1) rest memory (gas - 10) state substate returnData) :=
  (jumpi_zeroG hlt hbyte hgas).toHoare

/-- JUMPI on a condition equal to 0 goes to the next opcode, for 10 gas.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem jumpi_of_eq_zeroGA {destination condition : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x57) (hgas : 10 ≤ gas) (zero : condition = 0) :
    HoareGA fork
      (At code message pc (destination :: condition :: rest) memory gas state substate returnData)
      (At code message (pc + 1) rest memory (gas - 10) state substate returnData) := by
  subst zero
  exact jumpi_zeroGA hlt hbyte hgas

/-- JUMPI on a condition equal to 0 goes to the next opcode, for 10 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem jumpi_of_eq_zeroG {destination condition : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x57) (hgas : 10 ≤ gas) (zero : condition = 0) :
    HoareG fork
      (At code message pc (destination :: condition :: rest) memory gas state substate returnData)
      (At code message (pc + 1) rest memory (gas - 10) state substate returnData) :=
  (jumpi_of_eq_zeroGA hlt hbyte hgas zero).toG

/-- JUMPI on a condition equal to 0 goes to the next opcode, for 10 gas. -/
theorem jumpi_of_eq_zero {destination condition : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x57) (hgas : 10 ≤ gas) (zero : condition = 0) :
    Hoare fork
      (At code message pc (destination :: condition :: rest) memory gas state substate returnData)
      (At code message (pc + 1) rest memory (gas - 10) state substate returnData) :=
  (jumpi_of_eq_zeroG hlt hbyte hgas zero).toHoare

/-- JUMPI on a nonzero condition, to a JUMPDEST of the code, jumps there, for 10 gas.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem jumpi_takenGA {destination condition : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x57) (hgas : 10 ≤ gas) (nonzero : condition ≠ 0)
    (valid : isValidJumpDest (validJumpDestinations code) destination.toNat = true) :
    HoareGA fork
      (At code message pc (destination :: condition :: rest) memory gas state substate returnData)
      (At code message destination.toNat rest memory (gas - 10) state substate returnData) := by
  apply At.ruleGA hlt hbyte (ofByte_of_decode (op := .jumpi) rfl (Fork.frontier_le _))
    instruction_jumpi runMono_jumpi noAbort_jumpi
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [jumpiStep_of_isValidJumpDest hst nonzero (charge_nat (by rw [hg]; exact hgas))
    (by rw [hj]; exact valid)]
  exact ⟨_, rfl, hcode, hj, hm, rfl, rfl, hmem, by simp [hg, OPCODE_JUMPI, HIGH], hrun, herr,
    hout, hs, hss, hrd⟩

/-- JUMPI on a nonzero condition, to a JUMPDEST of the code, jumps there, for 10 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem jumpi_takenG {destination condition : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x57) (hgas : 10 ≤ gas) (nonzero : condition ≠ 0)
    (valid : isValidJumpDest (validJumpDestinations code) destination.toNat = true) :
    HoareG fork
      (At code message pc (destination :: condition :: rest) memory gas state substate returnData)
      (At code message destination.toNat rest memory (gas - 10) state substate returnData) :=
  (jumpi_takenGA hlt hbyte hgas nonzero valid).toG

/-- JUMPI on a nonzero condition, to a JUMPDEST of the code, jumps there, for 10 gas. -/
theorem jumpi_taken {destination condition : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x57) (hgas : 10 ≤ gas) (nonzero : condition ≠ 0)
    (valid : isValidJumpDest (validJumpDestinations code) destination.toNat = true) :
    Hoare fork
      (At code message pc (destination :: condition :: rest) memory gas state substate returnData)
      (At code message destination.toNat rest memory (gas - 10) state substate returnData) :=
  (jumpi_takenG hlt hbyte hgas nonzero valid).toHoare

/-- MSTORE writes a word at an offset of memory, after memory grows to hold it.

It pays 3 and the growth of memory.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem mstoreGA {start value : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x52)
    (hgas : 3 + (extendMemory memory.size [(start, 32)]).cost ≤ gas) :
    HoareGA fork (At code message pc (start :: value :: rest) memory gas state substate returnData)
      (At code message (pc + 1) rest
        (memoryWrite (memoryExtend memory (extendMemory memory.size [(start, 32)]).expandBy)
          start.toNat (wordBytes value))
        (gas - (3 + (extendMemory memory.size [(start, 32)]).cost)) state substate returnData) := by
  apply At.ruleGA hlt hbyte (ofByte_of_decode (op := .mstore) rfl (Fork.frontier_le _))
    instruction_mstore runMono_mstore noAbort_mstore
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  subst hmem hg
  have hcost : OPCODE_MSTORE_BASE = 3 := rfl
  rw [mstoreStep_cons hst]
  dsimp only
  rw [hcost, charge_nat hgas]
  refine ⟨_, rfl, hcode, hj, hm, by simp [hpc], ?_, ?_, ?_, hrun, herr, hout, hs, hss, hrd⟩
  · show rest = rest
    rfl
  · simp
  · simp

/-- MSTORE writes a word at an offset of memory, after memory grows to hold it.

It pays 3 and the growth of memory.

It holds over the steps from frames that are monotone in gas. -/
theorem mstoreG {start value : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x52)
    (hgas : 3 + (extendMemory memory.size [(start, 32)]).cost ≤ gas) :
    HoareG fork (At code message pc (start :: value :: rest) memory gas state substate returnData)
      (At code message (pc + 1) rest
        (memoryWrite (memoryExtend memory (extendMemory memory.size [(start, 32)]).expandBy)
          start.toNat (wordBytes value))
        (gas - (3 + (extendMemory memory.size [(start, 32)]).cost)) state substate returnData) :=
  (mstoreGA hlt hbyte hgas).toG

/-- MSTORE writes a word at an offset of memory, after memory grows to hold it.

It pays 3 and the growth of memory. -/
theorem mstore {start value : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x52)
    (hgas : 3 + (extendMemory memory.size [(start, 32)]).cost ≤ gas) :
    Hoare fork (At code message pc (start :: value :: rest) memory gas state substate returnData)
      (At code message (pc + 1) rest
        (memoryWrite (memoryExtend memory (extendMemory memory.size [(start, 32)]).expandBy)
          start.toNat (wordBytes value))
        (gas - (3 + (extendMemory memory.size [(start, 32)]).cost)) state substate returnData) :=
  (mstoreG hlt hbyte hgas).toHoare

/-- KECCAK256 puts the hash of a range of memory in place of its start and its size.

It pays its price on the bytes it hashes, and the growth of memory.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem keccak256GA {start size : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x20)
    (hgas :
      keccak256Cost size + (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    HoareGA fork (At code message pc (start :: size :: rest) memory gas state substate returnData)
      (At code message (pc + 1)
        (keccak (memoryReadBytes
          (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat size.toNat) :: rest)
        (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
        (gas - (keccak256Cost size + (extendMemory memory.size [(start, size)]).cost))
        state substate returnData) := by
  apply At.ruleGA hlt hbyte (ofByte_of_decode (op := .keccak256) rfl (Fork.frontier_le _))
    instruction_keccak256 runMono_keccak256 noAbort_keccak256
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  subst hmem hg
  rw [keccak256Step_cons hst]
  dsimp only
  rw [charge_nat hgas]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, rfl, rfl, hrun, herr, hout, hs, hss, hrd⟩

/-- KECCAK256 puts the hash of a range of memory in place of its start and its size.

It pays its price on the bytes it hashes, and the growth of memory.

It holds over the steps from frames that are monotone in gas. -/
theorem keccak256G {start size : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x20)
    (hgas :
      keccak256Cost size + (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    HoareG fork (At code message pc (start :: size :: rest) memory gas state substate returnData)
      (At code message (pc + 1)
        (keccak (memoryReadBytes
          (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat size.toNat) :: rest)
        (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
        (gas - (keccak256Cost size + (extendMemory memory.size [(start, size)]).cost))
        state substate returnData) :=
  (keccak256GA hlt hbyte hgas).toG

/-- KECCAK256 puts the hash of a range of memory in place of its start and its size.

It pays its price on the bytes it hashes, and the growth of memory. -/
theorem keccak256 {start size : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x20)
    (hgas :
      keccak256Cost size + (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    Hoare fork (At code message pc (start :: size :: rest) memory gas state substate returnData)
      (At code message (pc + 1)
        (keccak (memoryReadBytes
          (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat size.toNat) :: rest)
        (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
        (gas - (keccak256Cost size + (extendMemory memory.size [(start, size)]).cost))
        state substate returnData) :=
  (keccak256G hlt hbyte hgas).toHoare

/-- The price of SLOAD from Berlin: 2100 for a cold slot and 100 for a warm one, by EIP-2929. -/
theorem sloadCost_of_berlin (h : .berlin ≤ fork) (cold : Bool) :
    sloadCost fork cold = if cold then 2100 else 100 := by
  simp [sloadCost, h, COLD_STORAGE_ACCESS, WARM_ACCESS]

/-- From Berlin, SLOAD puts the word of a slot of the current account in place of its key.

The slot is cold when the transaction has not accessed it yet.

It pays 2100 for a cold slot and 100 for a warm one, then records the slot as accessed and read.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem sloadGA (hfork : .berlin ≤ fork) {key : U256} {rest : List U256} {cold : Bool}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x54)
    (hcold : decide (U256.toBeBytes key ∉
      substate.accessedStorageKeys.getD message.currentTarget ∅) = cold)
    (hgas : (if cold then 2100 else 100) ≤ gas) :
    HoareGA fork (At code message pc (key :: rest) memory gas state substate returnData)
      (At code message (pc + 1)
        (state.getStorage message.currentTarget (U256.toBeBytes key) :: rest) memory
        (gas - if cold then 2100 else 100)
        (state.recordStorageRead message.currentTarget (U256.toBeBytes key))
        { substate with
          accessedStorageKeys := (substate.accessedStorageKeys.insert message.currentTarget
            ((substate.accessedStorageKeys.getD message.currentTarget ∅).insert
              (U256.toBeBytes key))) } returnData) := by
  apply At.ruleGA hlt hbyte (ofByte_of_decode (op := .sload) rfl (Fork.frontier_le _))
    instruction_sload runMono_sload noAbort_sload
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  subst hm hg hs hss
  rw [sloadStep_cons hst]
  simp only [accessStorageKey, hfork, ↓reduceIte, hcold, sloadCost_of_berlin hfork]
  rw [charge_nat hgas]
  refine ⟨_, rfl, hcode, hj, rfl, by simp [hpc], ?_, hmem, ?_, hrun, herr, hout, rfl, rfl, hrd⟩
  · show _ :: rest = _ :: rest
    rfl
  · simp

/-- From Berlin, SLOAD puts the word of a slot of the current account in place of its key.

The slot is cold when the transaction has not accessed it yet.

It pays 2100 for a cold slot and 100 for a warm one, then records the slot as accessed and read.

It holds over the steps from frames that are monotone in gas. -/
theorem sloadG (hfork : .berlin ≤ fork) {key : U256} {rest : List U256} {cold : Bool}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x54)
    (hcold : decide (U256.toBeBytes key ∉
      substate.accessedStorageKeys.getD message.currentTarget ∅) = cold)
    (hgas : (if cold then 2100 else 100) ≤ gas) :
    HoareG fork (At code message pc (key :: rest) memory gas state substate returnData)
      (At code message (pc + 1)
        (state.getStorage message.currentTarget (U256.toBeBytes key) :: rest) memory
        (gas - if cold then 2100 else 100)
        (state.recordStorageRead message.currentTarget (U256.toBeBytes key))
        { substate with
          accessedStorageKeys := (substate.accessedStorageKeys.insert message.currentTarget
            ((substate.accessedStorageKeys.getD message.currentTarget ∅).insert
              (U256.toBeBytes key))) } returnData) :=
  (sloadGA hfork hlt hbyte hcold hgas).toG

/-- From Berlin, SLOAD puts the word of a slot of the current account in place of its key.

The slot is cold when the transaction has not accessed it yet.

It pays 2100 for a cold slot and 100 for a warm one, then records the slot as accessed and read. -/
theorem sload (hfork : .berlin ≤ fork) {key : U256} {rest : List U256} {cold : Bool}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x54)
    (hcold : decide (U256.toBeBytes key ∉
      substate.accessedStorageKeys.getD message.currentTarget ∅) = cold)
    (hgas : (if cold then 2100 else 100) ≤ gas) :
    Hoare fork (At code message pc (key :: rest) memory gas state substate returnData)
      (At code message (pc + 1)
        (state.getStorage message.currentTarget (U256.toBeBytes key) :: rest) memory
        (gas - if cold then 2100 else 100)
        (state.recordStorageRead message.currentTarget (U256.toBeBytes key))
        { substate with
          accessedStorageKeys := (substate.accessedStorageKeys.insert message.currentTarget
            ((substate.accessedStorageKeys.getD message.currentTarget ∅).insert
              (U256.toBeBytes key))) } returnData) :=
  (sloadG hfork hlt hbyte hcold hgas).toHoare

/-- What a stopped frame holds: whether it reverted, its output, its gas, state and substate. -/
def Halted (reverted : Bool) (output : ByteArray) (gas : Nat) (state : State.TransactionState)
    (substate : Substate) (evm : Evm fork Nat) : Prop :=
  evm.running = false ∧ evm.error = (if reverted then some .revert else none) ∧
    evm.output = output ∧ evm.gas = gas ∧ evm.state = state ∧ evm.substate = substate

/-- STOP stops the frame with no error and an empty output, at no price.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem stopGA (hlt : pc < code.size) (hbyte : code[pc] = 0x00) :
    SpecGA fork (At code message pc stack memory gas state substate returnData)
      (Halted false .empty gas state substate) := by
  apply At.ruleGA hlt hbyte (ofByte_of_decode (op := .stop) rfl (Fork.frontier_le _)) rfl
    runMono_stop noAbort_stop
  rintro evm ⟨-, -, -, -, -, -, hg, -, herr, hout, hs, hss, -⟩
  exact ⟨_, stopStep_eq evm, rfl, rfl, herr, hout, hg, hs, hss⟩

/-- STOP stops the frame with no error and an empty output, at no price.

It holds over the steps from frames that are monotone in gas. -/
theorem stopG (hlt : pc < code.size) (hbyte : code[pc] = 0x00) :
    SpecG fork (At code message pc stack memory gas state substate returnData)
      (Halted false .empty gas state substate) :=
  (stopGA hlt hbyte).toG

/-- STOP stops the frame with no error and an empty output, at no price. -/
theorem stop (hlt : pc < code.size) (hbyte : code[pc] = 0x00) :
    Spec fork (At code message pc stack memory gas state substate returnData)
      (Halted false .empty gas state substate) :=
  (stopG hlt hbyte).toSpec

/-- A frame at or past the end of its code stops as STOP does, at no price. -/
theorem stop_of_size_le (hle : code.size ≤ pc) :
    Spec fork (At code message pc stack memory gas state substate returnData)
      (Halted false .empty gas state substate) := by
  apply Triple.of_step
  rintro evm ⟨hcode, -, -, hpc, -, -, hg, hrun, herr, hout, hs, hss, -⟩
  exact ⟨_, .next hrun (step_of_size_le (by rw [hcode, hpc]; exact hle)), rfl, rfl, herr, hout,
    hg, hs, hss⟩

/-- RETURN stops the frame with a range of memory as its output, and pays the growth of memory.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem returnGA {start size : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0xf3) (hgas : (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    SpecGA fork (At code message pc (start :: size :: rest) memory gas state substate returnData)
      (Halted false
        (memoryReadBytes (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat size.toNat)
        (gas - (extendMemory memory.size [(start, size)]).cost) state substate) := by
  apply At.ruleGA hlt hbyte (ofByte_of_decode (op := .«return») rfl (Fork.frontier_le _))
    instruction_return runMono_return noAbort_return
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, -⟩
  subst hmem hg
  rw [returnStep_cons hst]
  dsimp only
  rw [charge_nat hgas]
  exact ⟨_, rfl, rfl, rfl, herr, rfl, by simp, hs, hss⟩

/-- RETURN stops the frame with a range of memory as its output, and pays the growth of memory.

It holds over the steps from frames that are monotone in gas. -/
theorem returnG {start size : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0xf3) (hgas : (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    SpecG fork (At code message pc (start :: size :: rest) memory gas state substate returnData)
      (Halted false
        (memoryReadBytes (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat size.toNat)
        (gas - (extendMemory memory.size [(start, size)]).cost) state substate) :=
  (returnGA hlt hbyte hgas).toG

/-- RETURN stops the frame with a range of memory as its output, and pays the growth of memory. -/
theorem «return» {start size : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0xf3) (hgas : (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    Spec fork (At code message pc (start :: size :: rest) memory gas state substate returnData)
      (Halted false
        (memoryReadBytes (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat size.toNat)
        (gas - (extendMemory memory.size [(start, size)]).cost) state substate) :=
  (returnG hlt hbyte hgas).toSpec

/-- From Byzantium, REVERT stops the frame with the revert error and a range of memory as output.

It pays the growth of memory, and keeps the gas left.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem revertGA (hfork : .byzantium ≤ fork) {start size : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xfd)
    (hgas : (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    SpecGA fork (At code message pc (start :: size :: rest) memory gas state substate returnData)
      (Halted true
        (memoryReadBytes (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat size.toNat)
        (gas - (extendMemory memory.size [(start, size)]).cost) state substate) := by
  apply At.ruleGA hlt hbyte (ofByte_of_decode (op := .revert) rfl hfork)
    (instruction_revert hfork) runMono_revert noAbort_revert
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, -⟩
  subst hmem hg
  rw [revertStep_eq, returnStep_cons hst]
  dsimp only
  rw [charge_nat hgas]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, by simp, hs, hss⟩

/-- From Byzantium, REVERT stops the frame with the revert error and a range of memory as output.

It pays the growth of memory, and keeps the gas left.

It holds over the steps from frames that are monotone in gas. -/
theorem revertG (hfork : .byzantium ≤ fork) {start size : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xfd)
    (hgas : (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    SpecG fork (At code message pc (start :: size :: rest) memory gas state substate returnData)
      (Halted true
        (memoryReadBytes (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat size.toNat)
        (gas - (extendMemory memory.size [(start, size)]).cost) state substate) :=
  (revertGA hfork hlt hbyte hgas).toG

/-- From Byzantium, REVERT stops the frame with the revert error and a range of memory as output.

It pays the growth of memory, and keeps the gas left. -/
theorem revert (hfork : .byzantium ≤ fork) {start size : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xfd)
    (hgas : (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    Spec fork (At code message pc (start :: size :: rest) memory gas state substate returnData)
      (Halted true
        (memoryReadBytes (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat size.toNat)
        (gas - (extendMemory memory.size [(start, size)]).cost) state substate) :=
  (revertG hfork hlt hbyte hgas).toSpec

/-! ## SSTORE -/

/-- SSTORE runs the write of a word of storage. -/
theorem instruction_sstore : instruction (Meter := Nat) fork .sstore = some sstoreStep := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, accountStep, storageStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- The step of SSTORE from Berlin, with one counter of gas, in a frame that may change the state.

It pops a key and a word, marks the slot of the current account accessed, and records its read.

It pays execution gas and state gas, from the original, current and new words and the cold flag.

Before Glamsterdam, the state gas is zero.

It writes the word, and adds the refund of the write to the refund counter.

The frame keeps its output and its return data. -/
theorem sstoreStep_eq (hfork : .berlin ≤ fork)
    {evm : Evm fork Nat} {key new : U256} {rest : List U256} {state' : State.TransactionState}
    (hst : evm.stack.val = key :: new :: rest) (hstatic : evm.message.isStatic = false)
    (hstipend : CALL_STIPEND < evm.gas)
    (hgas : sstoreTotalCost fork
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
      after.gas = evm.gas - sstoreTotalCost fork
        (evm.state.getStorageOriginal evm.message.currentTarget (U256.toBeBytes key))
        (evm.state.getStorage evm.message.currentTarget (U256.toBeBytes key)) new
        (decide (U256.toBeBytes key ∉
          evm.substate.accessedStorageKeys.getD evm.message.currentTarget ∅)) ∧
      after.running = evm.running ∧ after.error = evm.error ∧ after.output = evm.output ∧
      after.state = state' ∧ after.substate = { evm.substate with
        accessedStorageKeys := evm.substate.accessedStorageKeys.insert evm.message.currentTarget
          ((evm.substate.accessedStorageKeys.getD evm.message.currentTarget ∅).insert
            (U256.toBeBytes key))
        refundCounter := evm.substate.refundCounter + sstoreRefund fork
          (evm.state.getStorageOriginal evm.message.currentTarget (U256.toBeBytes key))
          (evm.state.getStorage evm.message.currentTarget (U256.toBeBytes key)) new } ∧
      after.returnData = evm.returnData := by
  have hist : Fork.istanbul ≤ fork := Nat.le_trans (by decide) hfork
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst hstatic hstipend hgas hset ⊢
  subst hst
  let original := state.getStorageOriginal message.currentTarget (U256.toBeBytes key)
  let current := state.getStorage message.currentTarget (U256.toBeBytes key)
  let cold := !decide (U256.toBeBytes key ∈
    substate.accessedStorageKeys.getD message.currentTarget ∅)
  have hgas' : sstoreCost fork original current new cold +
      sstoreStateGas fork original current new ≤ gas := by
    simpa [sstoreTotalCost, original, current, cold] using hgas
  have he : sstoreCost fork original current new cold ≤ gas := by omega
  have hs : sstoreStateGas fork original current new ≤
      gas - sstoreCost fork original current new cold := by omega
  dsimp only [original, current, cold] at he hs
  simp [sstoreStep, popWord, Stack.pop, bind, Except.bind, pure, Except.pure, hist,
    GasMeter.gasLeft, Nat.not_le.mpr hstipend, accessStorageKey, hfork, recordStorageRead,
    keepReads, refillStateGas, GasMeter.refill, chargeGas, GasMeter.charge, Nat.not_lt.mpr he,
    chargeStateGas, GasMeter.chargeState, Nat.not_lt.mpr hs, hstatic, hset,
    Except.mapError, advance, sstoreTotalCost, Nat.sub_sub]

/-- From Berlin, with one counter of gas, SSTORE writes a word to a slot of the current account.

The frame may change the state, and holds more than the stipend of 2300 gas, by EIP-2200.

The slot is cold when the transaction has not accessed it yet, by EIP-2929.

It pays execution gas and state gas, and adds the refund of the write.

Before Glamsterdam, the state gas is zero.

The write needs the account of the current address, and gives the state `state'`.

It holds over the steps from frames that are monotone in gas. -/
theorem sstoreG (hfork : .berlin ≤ fork) {key new : U256}
    {rest : List U256} {cold : Bool} {state' : State.TransactionState}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x55) (hstatic : message.isStatic = false)
    (hcold : decide (U256.toBeBytes key ∉
      substate.accessedStorageKeys.getD message.currentTarget ∅) = cold)
    (hstipend : CALL_STIPEND < gas)
    (hgas : sstoreTotalCost fork
      (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
      (state.getStorage message.currentTarget (U256.toBeBytes key)) new cold ≤ gas)
    (hset : (state.recordStorageRead message.currentTarget (U256.toBeBytes key)).setStorage
      message.currentTarget (U256.toBeBytes key) new = .ok state') :
    HoareG fork (At code message pc (key :: new :: rest) memory gas state substate returnData)
      (At code message (pc + 1) rest memory
        (gas - sstoreTotalCost fork
          (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
          (state.getStorage message.currentTarget (U256.toBeBytes key)) new cold)
        state'
        { substate with
          accessedStorageKeys := substate.accessedStorageKeys.insert message.currentTarget
            ((substate.accessedStorageKeys.getD message.currentTarget ∅).insert
              (U256.toBeBytes key))
          refundCounter := substate.refundCounter + sstoreRefund fork
            (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
            (state.getStorage message.currentTarget (U256.toBeBytes key)) new } returnData) := by
  apply At.ruleG hlt hbyte (ofByte_of_decode (op := .sstore) rfl (Fork.frontier_le _))
    instruction_sstore runMono_sstore
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  subst hm hg hs hss hcold
  obtain ⟨after, h, a1, a2, a3, a4, a5, a6, a7, a8, a9, ao, a10, a11, a12⟩ :=
    sstoreStep_eq hfork hst hstatic hstipend hgas hset
  exact ⟨after, h, by rw [a1, hcode], by rw [a2, hj], a3, by rw [a4, hpc], a5, by rw [a6, hmem],
    a7, by rw [a8, hrun], by rw [a9, herr], by rw [ao, hout], a10, a11, by rw [a12, hrd]⟩

/-- From Berlin, with one counter of gas, SSTORE writes a word to a slot of the current account.

The frame may change the state, and holds more than the stipend of 2300 gas, by EIP-2200.

The slot is cold when the transaction has not accessed it yet, by EIP-2929.

It pays execution gas and state gas, and adds the refund of the write.

Before Glamsterdam, the state gas is zero.

The write needs the account of the current address, and gives the state `state'`. -/
theorem sstore (hfork : .berlin ≤ fork) {key new : U256}
    {rest : List U256} {cold : Bool} {state' : State.TransactionState}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x55) (hstatic : message.isStatic = false)
    (hcold : decide (U256.toBeBytes key ∉
      substate.accessedStorageKeys.getD message.currentTarget ∅) = cold)
    (hstipend : CALL_STIPEND < gas)
    (hgas : sstoreTotalCost fork
      (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
      (state.getStorage message.currentTarget (U256.toBeBytes key)) new cold ≤ gas)
    (hset : (state.recordStorageRead message.currentTarget (U256.toBeBytes key)).setStorage
      message.currentTarget (U256.toBeBytes key) new = .ok state') :
    Hoare fork (At code message pc (key :: new :: rest) memory gas state substate returnData)
      (At code message (pc + 1) rest memory
        (gas - sstoreTotalCost fork
          (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
          (state.getStorage message.currentTarget (U256.toBeBytes key)) new cold)
        state'
        { substate with
          accessedStorageKeys := substate.accessedStorageKeys.insert message.currentTarget
            ((substate.accessedStorageKeys.getD message.currentTarget ∅).insert
              (U256.toBeBytes key))
          refundCounter := substate.refundCounter + sstoreRefund fork
            (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
            (state.getStorage message.currentTarget (U256.toBeBytes key)) new } returnData) :=
  (sstoreG hfork hlt hbyte hstatic hcold hstipend hgas hset).toHoare

/-- From Berlin, with one counter of gas, SSTORE to a slot of the current account, which exists.

The write then gives a state that holds `new` in the slot.

That state keeps every other slot of every address.

It also keeps the words before the transaction, the accounts, the codes and the block.

The rest is as for SSTORE: a frame that may change the state, more than 2300 gas, and the price. -/
theorem sstore_of_account (hfork : .berlin ≤ fork)
    {key new : U256} {rest : List U256} {cold : Bool}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x55) (hstatic : message.isStatic = false)
    (hcold : decide (U256.toBeBytes key ∉
      substate.accessedStorageKeys.getD message.currentTarget ∅) = cold)
    (hstipend : CALL_STIPEND < gas)
    (hgas : sstoreTotalCost fork
      (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
      (state.getStorage message.currentTarget (U256.toBeBytes key)) new cold ≤ gas)
    (hacc : (state.getAccountOptional message.currentTarget).isSome = true) :
    ∃ state' : State.TransactionState,
      state'.getStorage message.currentTarget (U256.toBeBytes key) = new ∧
      (∀ other slot, other ≠ message.currentTarget ∨ slot ≠ U256.toBeBytes key →
        state'.getStorage other slot = state.getStorage other slot) ∧
      state'.getStorageOriginal = state.getStorageOriginal ∧
      (∀ other, state'.getAccountOptional other = state.getAccountOptional other) ∧
      (∀ codeHash, state'.getCode codeHash = state.getCode codeHash) ∧
      state'.parent = state.parent ∧
      Hoare fork (At code message pc (key :: new :: rest) memory gas state substate returnData)
        (At code message (pc + 1) rest memory
          (gas - sstoreTotalCost fork
            (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
            (state.getStorage message.currentTarget (U256.toBeBytes key)) new cold)
          state'
          { substate with
            accessedStorageKeys := substate.accessedStorageKeys.insert message.currentTarget
              ((substate.accessedStorageKeys.getD message.currentTarget ∅).insert
                (U256.toBeBytes key))
            refundCounter := substate.refundCounter + sstoreRefund fork
              (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
              (state.getStorage message.currentTarget (U256.toBeBytes key)) new } returnData) := by
  -- Recording the read keeps the account, so the write succeeds.
  obtain ⟨state', hset⟩ := State.TransactionState.exists_setStorage (U256.toBeBytes key) new
    (tx := state.recordStorageRead message.currentTarget (U256.toBeBytes key))
    (by rw [(State.TransactionState.recordStorageRead_reads state _ message.currentTarget _
      (U256.toBeBytes key) default).1]; exact hacc)
  refine ⟨state', State.TransactionState.getStorage_setStorage_self hset, fun other slot hne => ?_,
    ?_, fun other => ?_, fun codeHash => ?_,
    by rw [State.TransactionState.parent_setStorage hset]; rfl,
    sstore hfork hlt hbyte hstatic hcold hstipend hgas hset⟩
  · rw [State.TransactionState.getStorage_setStorage_of_ne hset hne]
    exact (State.TransactionState.recordStorageRead_reads state _ other _ slot default).2.1
  · rw [State.TransactionState.getStorageOriginal_setStorage hset]
    funext other slot
    exact (State.TransactionState.recordStorageRead_reads state _ other _ slot default).2.2.1
  · rw [State.TransactionState.getAccountOptional_setStorage hset]
    exact (State.TransactionState.recordStorageRead_reads state _ other _
      (U256.toBeBytes key) default).1
  · rw [State.TransactionState.getCode_setStorage hset]
    exact (State.TransactionState.recordStorageRead_reads state _ message.currentTarget _
      (U256.toBeBytes key) codeHash).2.2.2.1

/-- Recording the access of a slot twice records it once. -/
theorem insert_insert_getD_self (substate : Substate) (address : Address) (key : Bytes32) :
    (substate.accessedStorageKeys.insert address
        ((substate.accessedStorageKeys.getD address ∅).insert key)).insert address
        (((substate.accessedStorageKeys.insert address
          ((substate.accessedStorageKeys.getD address ∅).insert key)).getD address ∅).insert key) =
      substate.accessedStorageKeys.insert address
        ((substate.accessedStorageKeys.getD address ∅).insert key) := by
  apply Std.ExtTreeMap.ext_getElem?
  intro other
  by_cases h : other = address
  · subst h
    simp only [Std.ExtTreeMap.getElem?_insert_self, Std.ExtTreeMap.getD_insert_self]
    congr 1
    ext x
    simp only [Std.ExtTreeSet.mem_insert]
    exact or_self_left
  · simp [Std.ExtTreeMap.getElem?_insert, Ne.symm h]

/-- A slot whose access is recorded is warm: it is among the accessed keys of its address. -/
theorem mem_insert_getD_self (substate : Substate) (address : Address) (key : Bytes32) :
    key ∈ (substate.accessedStorageKeys.insert address
      ((substate.accessedStorageKeys.getD address ∅).insert key)).getD address ∅ := by
  simp [Std.ExtTreeMap.getD_insert_self]

/-- Recording the access of a slot leaves every other slot as cold or warm as it was. -/
theorem mem_insert_getD_of_ne (substate : Substate) {address other : Address}
    {key slot : Bytes32} (hne : other ≠ address ∨ slot ≠ key) :
    slot ∈ (substate.accessedStorageKeys.insert address
      ((substate.accessedStorageKeys.getD address ∅).insert key)).getD other ∅ ↔
      slot ∈ substate.accessedStorageKeys.getD other ∅ := by
  by_cases h : other = address
  · subst h
    have hk : slot ≠ key := hne.resolve_left (fun h => h rfl)
    simp only [Std.ExtTreeMap.getD_insert_self, Std.ExtTreeSet.mem_insert]
    exact ⟨fun h => h.resolve_left fun he => hk (Std.compare_eq_iff_eq.mp he).symm, Or.inr⟩
  · simp [Std.ExtTreeMap.getD_insert, Ne.symm h]

/-- From Berlin, SLOAD costs at least 100, the price of a warm slot. -/
theorem le_sloadCost (hfork : .berlin ≤ fork) (cold : Bool) : 100 ≤ sloadCost fork cold := by
  rw [sloadCost_of_berlin hfork]
  cases cold <;> decide

/-- GAS pushes the gas left after its own price of 2, for 2 gas.

The word is the gas left modulo `2 ^ 256`. -/
theorem gas_rule (hlt : pc < code.size) (hbyte : code[pc] = 0x5a) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 (gas - 2) :: stack) memory (gas - 2) state
        substate returnData) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .gas) rfl (Fork.frontier_le _)) rfl
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [readFrame_of_length_lt (by rw [hst]; exact hstack),
    charge_nat (by rw [hg, show OPCODE_GAS = 2 from rfl]; exact hgas)]
  refine ⟨_, rfl, hcode, hj, hm, by simp [hpc], ?_, hmem, by simp [hg, OPCODE_GAS, BASE], hrun,
    herr, hout, hs, hss, hrd⟩
  simp [hst, hg, OPCODE_GAS, BASE, GasMeter.gasLeft]

/-- From Berlin to before Glamsterdam, a read of another account costs 2600 cold and 100 warm.

These are the prices of EIP-2929; from Glamsterdam, EIP-8038 changes them. -/
theorem externalBaseCost_of_berlin (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (cold : Bool) : externalBaseCost fork cold = if cold then 2600 else 100 := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  simp [externalBaseCost, hfork, hng, accountAccessCost, gasSchedule, WARM_ACCESS]

/-- From Berlin, EXTCODESIZE pushes the size of the code of an account.

The address is the low 20 bytes of the word, and the state holds the code `c` of its account.

The address is cold when the transaction has not accessed it yet, by EIP-2929.

Up to BPO5 it pays 2600 for a cold address and 100 for a warm one.

From Glamsterdam it pays the access to the address and a warm access to read the code, by EIP-8038.

It then adds the address to the accessed addresses, and records the read of the account. -/
theorem extcodesize_of_berlin_le (hfork : .berlin ≤ fork) {word : U256} {rest : List U256}
    {cold : Bool} {c : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0x3b)
    (hcode : state.getCode (state.getAccount (Base.toAddressMasked word)).codeHash = .ok c)
    (hcold : decide (Base.toAddressMasked word ∉ substate.accessedAddresses) = cold)
    (hgas : externalBaseCost fork cold ≤ gas) :
    Hoare fork (At code message pc (word :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 c.size :: rest) memory
        (gas - externalBaseCost fork cold)
        (state.recordAccountRead (Base.toAddressMasked word))
        { substate with
          accessedAddresses :=
            substate.accessedAddresses.insert (Base.toAddressMasked word) } returnData) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .extcodesize) rfl (Fork.frontier_le _)) rfl
  rintro evm ⟨hc, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  have found : accountCode evm (Base.toAddressMasked word) = .ok c := by
    simp [accountCode, hs, hcode, Except.mapError]
  rw [extcodesizeStep_of_accountCode hst found]
  simp only [accessAddress, hfork, ↓reduceIte, hss, hcold, hg, charge_nat hgas]
  exact ⟨_, rfl, hc, hj, hm, by simp [hpc], rfl, hmem, rfl, hrun, herr, hout, by simp [hs],
    by simp, hrd⟩

/-- From Berlin to before Glamsterdam, EXTCODESIZE pushes the size of the code of an account.

The address is the low 20 bytes of the word, and the state holds the code `c` of its account.

The address is cold when the transaction has not accessed it yet, by EIP-2929.

It pays 2600 for a cold address and 100 for a warm one.

It then adds the address to the accessed addresses, and records the read of the account. -/
theorem extcodesize (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {word : U256}
    {rest : List U256} {cold : Bool} {c : ByteArray} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x3b)
    (hcode : state.getCode (state.getAccount (Base.toAddressMasked word)).codeHash = .ok c)
    (hcold : decide (Base.toAddressMasked word ∉ substate.accessedAddresses) = cold)
    (hgas : (if cold then 2600 else 100) ≤ gas) :
    Hoare fork (At code message pc (word :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 c.size :: rest) memory
        (gas - if cold then 2600 else 100)
        (state.recordAccountRead (Base.toAddressMasked word))
        { substate with
          accessedAddresses :=
            substate.accessedAddresses.insert (Base.toAddressMasked word) } returnData) := by
  rw [← externalBaseCost_of_berlin hfork hglam cold] at hgas ⊢
  exact extcodesize_of_berlin_le hfork hlt hbyte hcode hcold hgas

end EthLib.Execution.Evm.Logic
