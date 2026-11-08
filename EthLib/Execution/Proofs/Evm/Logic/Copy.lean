module

public import EthLib.Execution.Proofs.Evm.Logic.Rules
public import EthLib.Execution.Proofs.Evm.Instructions.AccountData

/-!
# Proofs: rules for the opcodes that write bytes to memory

Each rule grows memory to hold the range it writes, pays that growth, then writes the bytes.

- MSTORE8 writes the lowest byte of a word, for 3 gas.
- MCOPY, from Dencun, copies a range of memory, for 3 gas and 3 gas a word, by EIP-5656.
- CALLDATACOPY and CODECOPY copy a range of the call data or the code, for 3 gas and 3 gas a word.
- RETURNDATACOPY, from Byzantium, copies a range of the return data, for 3 gas and 3 gas a word.
- EXTCODECOPY copies a range of the code of an account, for its access and 3 gas a word.

A copy from the call data or a code reads zeros past its end.

RETURNDATACOPY fails when its range ends past the return data, by EIP-211.

So its rule asks that the range fit.

MCOPY grows memory to hold both its ranges, and reads its source after that growth.

The rule for EXTCODECOPY holds from Berlin to before Glamsterdam, with the prices of EIP-2929.

Sources: EIP-211, EIP-2929 and EIP-5656.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}
  {returnData : ByteArray}

/-- MSTORE8 runs the store of a byte to memory. -/
theorem instruction_mstore8 : instruction (Meter := Nat) fork .mstore8 = some mstore8Step := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, HOrElse.hOrElse,
    OrElse.orElse, Option.orElse]

/-- MCOPY runs the copy of a range of memory. -/
theorem instruction_mcopy : instruction (Meter := Nat) fork .mcopy = some mcopyStep := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, HOrElse.hOrElse,
    OrElse.orElse, Option.orElse]

/-- CALLDATACOPY runs the copy of the call data to memory. -/
theorem instruction_calldatacopy : instruction (Meter := Nat) fork .calldatacopy =
    some fun evm => copyToMemory OPCODE_CALLDATACOPY_BASE evm.message.data evm := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, HOrElse.hOrElse,
    OrElse.orElse, Option.orElse]

/-- CODECOPY runs the copy of the code to memory. -/
theorem instruction_codecopy : instruction (Meter := Nat) fork .codecopy =
    some fun evm => copyToMemory OPCODE_CODECOPY_BASE evm.code evm := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, HOrElse.hOrElse,
    OrElse.orElse, Option.orElse]

/-- RETURNDATACOPY runs the copy of the return data to memory. -/
theorem instruction_returndatacopy :
    instruction (Meter := Nat) fork .returndatacopy = some returndatacopyStep := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, HOrElse.hOrElse,
    OrElse.orElse, Option.orElse]

/-- EXTCODECOPY runs the copy of the code of an account to memory. -/
theorem instruction_extcodecopy :
    instruction (Meter := Nat) fork .extcodecopy = some extcodecopyStep := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, accountStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- MSTORE8 writes the lowest byte of a word at an offset, after memory grows to hold it.

It pays 3 and the growth of memory. -/
theorem mstore8 {start value : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x53)
    (hgas : 3 + (extendMemory memory.size [(start, 1)]).cost ≤ gas) :
    Hoare fork (At code message pc (start :: value :: rest) memory gas state substate returnData)
      (At code message (pc + 1) rest
        (memoryWrite (memoryExtend memory (extendMemory memory.size [(start, 1)]).expandBy)
          start.toNat ⟨#[UInt8.ofNat value.toNat]⟩)
        (gas - (3 + (extendMemory memory.size [(start, 1)]).cost)) state substate returnData) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .mstore8) rfl (Fork.frontier_le _))
    instruction_mstore8
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  subst hmem hg
  have hcost : OPCODE_MSTORE8_BASE = 3 := rfl
  rw [mstore8Step_cons hst]
  dsimp only
  rw [hcost, charge_nat hgas]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, rfl, rfl, hrun, herr, hout, hs, hss, hrd⟩

/-- From Dencun, MCOPY copies a range of memory to a destination, by EIP-5656.

Memory first grows to hold both ranges, and the source is read after that growth.

It pays 3, 3 gas a word and the growth of memory. -/
theorem mcopy (hfork : .dencun ≤ fork) {destination source length : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x5e)
    (hgas : 3 + 3 * wordCount length.toNat +
      (extendMemory memory.size [(source, length), (destination, length)]).cost ≤ gas) :
    Hoare fork (At code message pc (destination :: source :: length :: rest) memory gas state
        substate returnData)
      (At code message (pc + 1) rest
        (memoryWrite (memoryExtend memory
            (extendMemory memory.size [(source, length), (destination, length)]).expandBy)
          destination.toNat
          (memoryReadBytes (memoryExtend memory
            (extendMemory memory.size [(source, length), (destination, length)]).expandBy)
            source.toNat length.toNat))
        (gas - (3 + 3 * wordCount length.toNat +
          (extendMemory memory.size [(source, length), (destination, length)]).cost))
        state substate returnData) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .mcopy) rfl hfork) instruction_mcopy
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  subst hmem hg
  have hcost : OPCODE_MCOPY_BASE = 3 := rfl
  have hword : OPCODE_COPY_PER_WORD = 3 := rfl
  rw [mcopyStep_cons hst]
  dsimp only
  rw [hcost, hword, charge_nat hgas]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, rfl, rfl, hrun, herr, hout, hs, hss, hrd⟩

/-- A copy of a buffer to memory, at the program counter of an opcode that runs it.

The copy reads the same buffer from every state that has the code and the message of the frame. -/
theorem copyWith {byte : UInt8} {op : Op} {base : Nat} {data : Evm fork Nat → ByteArray}
    {buffer : ByteArray} {start offset size : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = byte) (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction fork op = some fun evm => copyToMemory base (data evm) evm)
    (hdata : ∀ evm, evm.code = code → evm.message = message → data evm = buffer)
    (hgas : base + 3 * wordCount size.toNat + (extendMemory memory.size [(start, size)]).cost ≤
      gas) :
    Hoare fork (At code message pc (start :: offset :: size :: rest) memory gas state substate
        returnData)
      (At code message (pc + 1) rest
        (memoryWrite (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat ⟨(bufferRead buffer offset.toNat size.toNat).toArray⟩)
        (gas - (base + 3 * wordCount size.toNat + (extendMemory memory.size [(start, size)]).cost))
        state substate returnData) := by
  apply At.rule hlt hbyte decoded hrun
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun', herr, hout, hs, hss, hrd⟩
  have hword : OPCODE_COPY_PER_WORD = 3 := rfl
  rw [copyToMemory_cons hst, hdata evm hcode hm]
  dsimp only
  rw [hword, hmem, hg, charge_nat hgas]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, rfl, rfl, hrun', herr, hout, hs, hss, hrd⟩

/-- CALLDATACOPY copies a range of the call data to memory, with zeros past its end.

It pays 3, 3 gas a word and the growth of memory. -/
theorem calldatacopy {start offset size : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x37)
    (hgas : 3 + 3 * wordCount size.toNat + (extendMemory memory.size [(start, size)]).cost ≤
      gas) :
    Hoare fork (At code message pc (start :: offset :: size :: rest) memory gas state substate
        returnData)
      (At code message (pc + 1) rest
        (memoryWrite (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat ⟨(bufferRead message.data offset.toNat size.toNat).toArray⟩)
        (gas - (3 + 3 * wordCount size.toNat + (extendMemory memory.size [(start, size)]).cost))
        state substate returnData) :=
  copyWith (base := OPCODE_CALLDATACOPY_BASE) hlt hbyte
    (ofByte_of_decode (op := .calldatacopy) rfl (Fork.frontier_le _)) instruction_calldatacopy
    (fun _ _ hm => by rw [hm]) hgas

/-- CODECOPY copies a range of the code to memory, with zeros past its end.

It pays 3, 3 gas a word and the growth of memory. -/
theorem codecopy {start offset size : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x39)
    (hgas : 3 + 3 * wordCount size.toNat + (extendMemory memory.size [(start, size)]).cost ≤
      gas) :
    Hoare fork (At code message pc (start :: offset :: size :: rest) memory gas state substate
        returnData)
      (At code message (pc + 1) rest
        (memoryWrite (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat ⟨(bufferRead code offset.toNat size.toNat).toArray⟩)
        (gas - (3 + 3 * wordCount size.toNat + (extendMemory memory.size [(start, size)]).cost))
        state substate returnData) :=
  copyWith (base := OPCODE_CODECOPY_BASE) hlt hbyte
    (ofByte_of_decode (op := .codecopy) rfl (Fork.frontier_le _)) instruction_codecopy
    (fun _ hc _ => hc) hgas

/-- From Byzantium, RETURNDATACOPY copies a range of the return data to memory, by EIP-211.

The range ends within the return data.

It pays 3, 3 gas a word and the growth of memory, and keeps the return data. -/
theorem returndatacopy (hfork : .byzantium ≤ fork) {start offset size : U256}
    {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0x3e)
    (fit : offset.toNat + size.toNat ≤ returnData.size)
    (hgas : 3 + 3 * wordCount size.toNat + (extendMemory memory.size [(start, size)]).cost ≤
      gas) :
    Hoare fork
      (At code message pc (start :: offset :: size :: rest) memory gas state substate returnData)
      (At code message (pc + 1) rest
        (memoryWrite (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat (memoryReadBytes returnData offset.toNat size.toNat))
        (gas - (3 + 3 * wordCount size.toNat + (extendMemory memory.size [(start, size)]).cost))
        state substate returnData) := by
  apply Triple.of_step
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  have hcost : OPCODE_RETURNDATACOPY_BASE = 3 := rfl
  have hword : OPCODE_RETURNDATACOPY_PER_WORD = 3 := rfl
  have ok := returndatacopyStep_cons hst (by rw [hrd]; exact fit)
  rw [hrd] at ok
  dsimp only at ok
  rw [hcost, hword, hmem, hg, charge_nat hgas] at ok
  exact ⟨_, Step.of_code hrun hcode hpc hlt hbyte
      (ofByte_of_decode (op := .returndatacopy) rfl hfork) instruction_returndatacopy ok,
    ⟨hcode, hj, hm, by simp [hpc], rfl, rfl, rfl, hrun, herr, hout, hs, hss, rfl⟩⟩

/-- From Berlin, EXTCODECOPY copies a range of the code of an account.

The address is the low 20 bytes of the word, and the state holds the code `c` of its account.

The code reads as zeros past its end.

The address is cold when the transaction has not accessed it yet, by EIP-2929.

Up to BPO5 it pays 2600 for a cold address and 100 for a warm one.

From Glamsterdam it pays the access to the address and a warm access to read the code, by EIP-8038.

It also pays 3 gas a word and the growth of memory.

It then adds the address to the accessed addresses, and records the read of the account. -/
theorem extcodecopy_of_berlin_le (hfork : .berlin ≤ fork)
    {word start offset size : U256} {rest : List U256} {cold : Bool} {c : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x3c)
    (hcode : state.getCode (state.getAccount (Base.toAddressMasked word)).codeHash = .ok c)
    (hcold : decide (Base.toAddressMasked word ∉ substate.accessedAddresses) = cold)
    (hgas : externalBaseCost fork cold + 3 * wordCount size.toNat +
      (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    Hoare fork
      (At code message pc (word :: start :: offset :: size :: rest) memory gas state substate
        returnData)
      (At code message (pc + 1) rest
        (memoryWrite (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat ⟨(bufferRead c offset.toNat size.toNat).toArray⟩)
        (gas - (externalBaseCost fork cold + 3 * wordCount size.toNat +
          (extendMemory memory.size [(start, size)]).cost))
        (state.recordAccountRead (Base.toAddressMasked word))
        { substate with
          accessedAddresses :=
            substate.accessedAddresses.insert (Base.toAddressMasked word) } returnData) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .extcodecopy) rfl (Fork.frontier_le _))
    instruction_extcodecopy
  rintro evm ⟨hc, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  have found : accountCode evm (Base.toAddressMasked word) = .ok c := by
    simp [accountCode, hs, hcode, Except.mapError]
  have hword : OPCODE_COPY_PER_WORD = 3 := rfl
  rw [extcodecopyStep_of_accountCode hst found]
  simp only [accessAddress, hfork, ↓reduceIte, hss, hcold, hword, hg, hmem, charge_nat hgas]
  exact ⟨_, rfl, hc, hj, hm, by simp [hpc], rfl, rfl, rfl, hrun, herr, hout, by simp [hs],
    by simp, hrd⟩

/-- From Berlin to before Glamsterdam, EXTCODECOPY copies a range of the code of an account.

The address is the low 20 bytes of the word, and the state holds the code `c` of its account.

The code reads as zeros past its end.

The address is cold when the transaction has not accessed it yet, by EIP-2929.

It pays 2600 for a cold address and 100 for a warm one, 3 gas a word and the growth of memory.

It then adds the address to the accessed addresses, and records the read of the account. -/
theorem extcodecopy (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {word start offset size : U256} {rest : List U256} {cold : Bool} {c : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x3c)
    (hcode : state.getCode (state.getAccount (Base.toAddressMasked word)).codeHash = .ok c)
    (hcold : decide (Base.toAddressMasked word ∉ substate.accessedAddresses) = cold)
    (hgas : (if cold then 2600 else 100) + 3 * wordCount size.toNat +
      (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    Hoare fork
      (At code message pc (word :: start :: offset :: size :: rest) memory gas state substate
        returnData)
      (At code message (pc + 1) rest
        (memoryWrite (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat ⟨(bufferRead c offset.toNat size.toNat).toArray⟩)
        (gas - ((if cold then 2600 else 100) + 3 * wordCount size.toNat +
          (extendMemory memory.size [(start, size)]).cost))
        (state.recordAccountRead (Base.toAddressMasked word))
        { substate with
          accessedAddresses :=
            substate.accessedAddresses.insert (Base.toAddressMasked word) } returnData) := by
  rw [← externalBaseCost_of_berlin hfork hglam cold] at hgas ⊢
  exact extcodecopy_of_berlin_le hfork hlt hbyte hcode hcold hgas

end EthLib.Execution.Evm.Logic
