module

public import EthLib.Base.Proofs.BigEndian
public import EthLib.Base.Proofs.U256
public import EthLib.Execution.Evm.Instructions.MemoryData
public import EthLib.Execution.Proofs.Evm.Machine.Memory
public import EthLib.Execution.Proofs.Evm.Step

/-!
# Proofs: `Evm.Instructions.MemoryData`

A word that MSTORE writes reads back whole with MLOAD at the same offset.

MCOPY copies the old bytes of its source, also when the source and the destination overlap.

CALLDATALOAD reads the call data past its end as zeros.

MLOAD pays its price and the growth of memory, and CALLDATALOAD pays its price.

Then each puts the word it reads at the offset in place of the offset.

MLOAD reads after the growth of memory.

RETURNDATACOPY that pays fails exactly when its range ends past the return data.

None of these instructions changes the message, the state or the substate of the frame.

MSTORE, MSTORE8, MCOPY, CALLDATACOPY, CODECOPY and RETURNDATACOPY set each byte of their range.

They keep every other byte of memory.

Each instruction keeps the size of memory a multiple of 32.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256 bytesToNat natToBytes byteAt byteAt_append_zeros byteAt_eq_getD)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- A word has 32 bytes. -/
theorem size_wordBytes (word : U256) : (wordBytes word).size = 32 := by
  simp [wordBytes, ← ByteArray.size_data]

/-- The word of 32 bytes that a write of a word puts in memory is that word. -/
theorem loadWord_memoryWrite_wordBytes {memory : ByteArray} {start : Nat} (word : U256)
    (h : start + 32 ≤ memory.size) :
    loadWord (memoryReadBytes (memoryWrite memory start (wordBytes word)) start 32) 0 32 =
      word := by
  have hsize := size_wordBytes word
  rw [← hsize, memoryReadBytes_memoryWrite (by omega), loadWord, bufferRead_zero_size]
  have bytes : (wordBytes word).data.toList = natToBytes 32 word.toNat :=
    EthLib.Base.U256.toList_toBeBytes word
  have small : word.toNat < 256 ^ 32 := by
    have := word.isLt
    rwa [show (2 : Nat) ^ 256 = 256 ^ 32 by decide] at this
  rw [bytes, EthLib.Base.bytesToNat_natToBytes_of_lt small]
  apply BitVec.eq_of_toNat_eq
  simp

/-- MCOPY reads its source before it writes, so overlapping ranges copy the old bytes. -/
theorem memoryReadBytes_memoryWrite_memoryReadBytes {memory : ByteArray}
    {source destination length : Nat} (hs : source + length ≤ memory.size)
    (hd : destination + length ≤ memory.size) :
    memoryReadBytes (memoryWrite memory destination (memoryReadBytes memory source length))
        destination length =
      memoryReadBytes memory source length := by
  have hsize := size_memoryReadBytes hs
  have := memoryReadBytes_memoryWrite (memory := memory) (start := destination)
    (value := memoryReadBytes memory source length) (by omega)
  rwa [hsize] at this

/-- CALLDATALOAD reads the call data past its end as zeros. -/
theorem loadWord_append_zeros (data : ByteArray) (start size k : Nat) :
    loadWord (data ++ ByteArray.mk (Array.replicate k 0)) start size =
      loadWord data start size := by
  simp only [loadWord, bufferRead, byteAt_append_zeros]

/-- RETURNDATACOPY that pays fails exactly when its range ends past the return data. -/
theorem returndatacopyStep_eq_error_iff {evm : Evm fork Meter} {start offset size : U256}
    {rest : List U256} {gas : Meter} (h : evm.stack.val = start :: offset :: size :: rest)
    (paid : GasMeter.charge evm.gas
      (OPCODE_RETURNDATACOPY_BASE + OPCODE_RETURNDATACOPY_PER_WORD * wordCount size.toNat +
        (extendMemory evm.memory.size [(start, size)]).cost) = .ok gas) :
    returndatacopyStep evm = .error .outOfBoundsRead ↔
      evm.returnData.size < offset.toNat + size.toNat := by
  have hstack : evm.stack = ⟨start :: offset :: size :: rest, h ▸ evm.stack.property⟩ :=
    Subtype.ext h
  simp only [returndatacopyStep, popWord, chargeGas, hstack, Stack.pop]
  by_cases past : evm.returnData.size < offset.toNat + size.toNat <;>
    simp [paid, past, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- Each instruction that moves bytes keeps the message, the state, the substate and the code. -/
theorem memoryDataStep_sameContext {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : memoryDataStep op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : SameContext evm after := by
  cases op <;> simp only [memoryDataStep, Option.some.injEq, reduceCtorEq] at hstep <;>
    subst hstep
  case msize | calldatasize | codesize | returndatasize => exact readFrame_sameContext h
  case mload =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (((popWord_sameContext h1).trans (chargeGasAndMemory_sameContext h2)).trans
      (pushWord_sameContext h3)).advance
  case mstore | mstore8 =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have := ((popWord_sameContext h1).trans (popWord_sameContext h2)).trans
      (chargeGasAndMemory_sameContext h3)
    exact ⟨this.message, this.state, this.substate, this.code⟩
  case calldataload =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (((popWord_sameContext h1).trans (chargeGas_sameContext h2)).trans
      (pushWord_sameContext h3)).advance
  case mcopy | calldatacopy | codecopy =>
    first
      | simp only [mcopyStep] at h
      | simp only [copyToMemory] at h
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have := (((popWord_sameContext h1).trans (popWord_sameContext h2)).trans
      (popWord_sameContext h3)).trans (chargeGasAndMemory_sameContext h4)
    exact ⟨this.message, this.state, this.substate, this.code⟩
  case returndatacopy =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
    simp only [throw, throwThe, MonadExceptOf.throw] at h
    split at h
    · cases h
    · cases h
      have := (((popWord_sameContext h1).trans (popWord_sameContext h2)).trans
        (popWord_sameContext h3)).trans (chargeGas_sameContext h4)
      exact ⟨this.message, this.state, this.substate, this.code⟩

/-! ## The bytes that each instruction leaves in memory -/

/-- MSTORE sets the 32 bytes from its start to the bytes of the word, and keeps every other byte.

Memory must start at a size that is a multiple of 32. -/
theorem byteAt_mstoreStep {evm after : Evm fork Meter} {start value : U256} {rest : List U256}
    (hstack : evm.stack.val = start :: value :: rest) (hmod : evm.memory.size % 32 = 0)
    (h : mstoreStep evm = .ok after) (i : Nat) :
    byteAt after.memory i =
      if start.toNat ≤ i ∧ i < start.toNat + 32 then byteAt (wordBytes value) (i - start.toNat)
      else byteAt evm.memory i := by
  unfold mstoreStep at h
  obtain ⟨⟨x, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨y, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨rfl, s1, m1, -⟩ := popWord_of_stack hstack h1
  obtain ⟨rfl, -, m2, -⟩ := popWord_of_stack s1 h2
  have hmod2 : e2.memory.size % 32 = 0 := by rw [m2, m1]; exact hmod
  have fit := le_size_chargeGasAndMemory hmod2 h3 (start, 32) (List.mem_singleton_self _) (by simp)
  simp only [advance]
  rw [byteAt_memoryWrite (by rw [size_wordBytes]; exact fit), size_wordBytes]
  split
  · rfl
  · rw [byteAt_chargeGasAndMemory h3, m2, m1]

/-- MSTORE8 sets the byte at its start to the lowest byte of the word, and keeps every other byte.

Memory must start at a size that is a multiple of 32. -/
theorem byteAt_mstore8Step {evm after : Evm fork Meter} {start value : U256} {rest : List U256}
    (hstack : evm.stack.val = start :: value :: rest) (hmod : evm.memory.size % 32 = 0)
    (h : mstore8Step evm = .ok after) (i : Nat) :
    byteAt after.memory i =
      if i = start.toNat then UInt8.ofNat value.toNat else byteAt evm.memory i := by
  unfold mstore8Step at h
  obtain ⟨⟨x, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨y, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨rfl, s1, m1, -⟩ := popWord_of_stack hstack h1
  obtain ⟨rfl, -, m2, -⟩ := popWord_of_stack s1 h2
  have hmod2 : e2.memory.size % 32 = 0 := by rw [m2, m1]; exact hmod
  have fit := le_size_chargeGasAndMemory hmod2 h3 (start, 1) (List.mem_singleton_self _) (by simp)
  have hone : ({ data := #[UInt8.ofNat value.toNat] } : ByteArray).size = 1 := rfl
  simp only [advance]
  rw [byteAt_memoryWrite (by rw [hone]; exact fit), hone]
  by_cases hi : i = start.toNat
  · subst hi
    simp [byteAt, hone, ByteArray.getElem_eq_getElem_data]
  · rw [ite_eq_right_iff.mpr (fun hc => absurd (by omega) hi),
      ite_eq_right_iff.mpr (fun hc => absurd hc hi), byteAt_chargeGasAndMemory h3, m2, m1]

/-- MCOPY sets each byte of its destination range to the byte of the source range before the copy.

It keeps every other byte.

So an overlap of the two ranges copies the old bytes.

Memory must start at a size that is a multiple of 32. -/
theorem byteAt_mcopyStep {evm after : Evm fork Meter} {destination source length : U256}
    {rest : List U256} (hstack : evm.stack.val = destination :: source :: length :: rest)
    (hmod : evm.memory.size % 32 = 0) (h : mcopyStep evm = .ok after) (i : Nat) :
    byteAt after.memory i =
      if destination.toNat ≤ i ∧ i < destination.toNat + length.toNat then
        byteAt evm.memory (source.toNat + (i - destination.toNat))
      else byteAt evm.memory i := by
  unfold mcopyStep at h
  obtain ⟨⟨x, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨y, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨z, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨rfl, s1, m1, -⟩ := popWord_of_stack hstack h1
  obtain ⟨rfl, s2, m2, -⟩ := popWord_of_stack s1 h2
  obtain ⟨rfl, -, m3, -⟩ := popWord_of_stack s2 h3
  have hmem : ∀ j, byteAt e4.memory j = byteAt evm.memory j := fun j => by
    rw [byteAt_chargeGasAndMemory h4, m3, m2, m1]
  simp only [advance]
  by_cases hz : length = 0
  · subst hz
    simp [memoryReadBytes, memoryWrite, hmem]
    intro h1 h2
    omega
  · have hmod3 : e3.memory.size % 32 = 0 := by rw [m3, m2, m1]; exact hmod
    have fitSource := le_size_chargeGasAndMemory hmod3 h4 (source, length) (by simp) hz
    have fitDest := le_size_chargeGasAndMemory hmod3 h4 (destination, length) (by simp) hz
    simp only at fitSource fitDest
    have hsize := size_memoryReadBytes fitSource
    rw [byteAt_memoryWrite (by rw [hsize]; exact fitDest), hsize]
    split
    · rw [byteAt_memoryReadBytes fitSource, ite_eq_left_iff.mpr (fun hc => absurd (by omega) hc),
        hmem]
    · exact hmem i

/-- A copy to memory sets each byte of its range to the byte of the source from the offset.

Past the end of the source, the byte is zero.

The copy keeps every other byte.

CALLDATACOPY and CODECOPY run this copy.

Memory must start at a size that is a multiple of 32. -/
theorem byteAt_copyToMemory {base : Nat} {data : ByteArray} {evm after : Evm fork Meter}
    {start offset size : U256} {rest : List U256}
    (hstack : evm.stack.val = start :: offset :: size :: rest) (hmod : evm.memory.size % 32 = 0)
    (h : copyToMemory base data evm = .ok after) (i : Nat) :
    byteAt after.memory i =
      if start.toNat ≤ i ∧ i < start.toNat + size.toNat then
        byteAt data (offset.toNat + (i - start.toNat))
      else byteAt evm.memory i := by
  unfold copyToMemory at h
  obtain ⟨⟨x, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨y, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨z, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨rfl, s1, m1, -⟩ := popWord_of_stack hstack h1
  obtain ⟨rfl, s2, m2, -⟩ := popWord_of_stack s1 h2
  obtain ⟨rfl, -, m3, -⟩ := popWord_of_stack s2 h3
  have hmem : ∀ j, byteAt e4.memory j = byteAt evm.memory j := fun j => by
    rw [byteAt_chargeGasAndMemory h4, m3, m2, m1]
  have hlen : ({ data := (bufferRead data offset.toNat size.toNat).toArray } : ByteArray).size =
      size.toNat := by simp [ByteArray.size, bufferRead_length]
  simp only [advance]
  by_cases hz : size = 0
  · subst hz
    have hw : memoryWrite e4.memory start.toNat
        ⟨(bufferRead data offset.toNat (0 : U256).toNat).toArray⟩ = e4.memory := by
      unfold memoryWrite
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [hlen]; rfl))]
    rw [hw, hmem, ite_eq_right_iff.mpr (fun hc => absurd hc.2 (by have := hc.1; simp; omega))]
  · have hmod3 : e3.memory.size % 32 = 0 := by rw [m3, m2, m1]; exact hmod
    have fit := le_size_chargeGasAndMemory hmod3 h4 (start, size) (by simp) hz
    simp only at fit
    rw [byteAt_memoryWrite (by rw [hlen]; exact fit), hlen]
    split
    · rw [byteAt_bufferRead, ite_eq_left_iff.mpr (fun hc => absurd (by omega) hc)]
    · exact hmem i

/-- RETURNDATACOPY sets each byte of its range to the byte of the return data from the offset.

It keeps every other byte.

The range of the return data must fit, or the copy fails.

Memory must start at a size that is a multiple of 32. -/
theorem byteAt_returndatacopyStep {evm after : Evm fork Meter} {start offset size : U256}
    {rest : List U256} (hstack : evm.stack.val = start :: offset :: size :: rest)
    (hmod : evm.memory.size % 32 = 0) (h : returndatacopyStep evm = .ok after) (i : Nat) :
    byteAt after.memory i =
      if start.toNat ≤ i ∧ i < start.toNat + size.toNat then
        byteAt evm.returnData (offset.toNat + (i - start.toNat))
      else byteAt evm.memory i := by
  unfold returndatacopyStep at h
  obtain ⟨⟨x, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨y, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨z, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨rfl, s1, m1, d1⟩ := popWord_of_stack hstack h1
  obtain ⟨rfl, s2, m2, d2⟩ := popWord_of_stack s1 h2
  obtain ⟨rfl, -, m3, d3⟩ := popWord_of_stack s2 h3
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, -, rfl⟩ := chargeGas_eq_ok_iff_charge.mp h4
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · rename_i inside
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [advance]
    have hdata : e3.returnData = evm.returnData := by rw [d3, d2, d1]
    have hmem : e3.memory = evm.memory := by rw [m3, m2, m1]
    by_cases hz : size = 0
    · subst hz
      have hz0 : (0 : U256).toNat = 0 := rfl
      rw [show memoryReadBytes e3.returnData offset.toNat (0 : U256).toNat = .empty by
          simp [memoryReadBytes],
        show ∀ m : ByteArray, memoryWrite m start.toNat .empty = m from
          fun m => by simp [memoryWrite]]
      rw [byteAt_memoryExtend, hmem,
        ite_eq_right_iff.mpr (fun hc => absurd hc.2 (by have := hc.1; omega))]
    · have hcover := le_ceil32_add_expandBy e3.memory.size [(start, size)] (start, size)
        (List.mem_singleton_self _) hz
      rw [hmem, ceil32_of_mod hmod] at hcover
      have fitData : offset.toNat + size.toNat ≤ e3.returnData.size := Nat.le_of_not_gt inside
      have hsize := size_memoryReadBytes fitData
      rw [byteAt_memoryWrite (by rw [hsize, size_memoryExtend, hmem]; exact hcover), hsize]
      split
      · rw [byteAt_memoryReadBytes fitData, ite_eq_left_iff.mpr (fun hc => absurd (by omega) hc),
          hdata]
      · rw [byteAt_memoryExtend, hmem]

/-! ## The size of memory -/

/-- CALLDATALOAD on an offset: pay, then put the word of call data at the offset in its place. -/
theorem calldataloadStep_cons {evm : Evm fork Meter} {start : U256} {rest : List U256}
    (h : evm.stack.val = start :: rest) :
    calldataloadStep evm = (GasMeter.charge evm.gas OPCODE_CALLDATALOAD).map fun gas =>
      { evm with
        stack := ⟨loadWord evm.message.data start.toNat 32 :: rest,
          length_cons_le (dropped := [start]) h (by simp)⟩,
        gas, pc := evm.pc + 1 } := by
  have hstack : evm.stack = ⟨start :: rest, h ▸ evm.stack.property⟩ := Subtype.ext h
  have room : ¬(rest.length = STACK_LIMIT) := by
    have := length_cons_le (x := start) (dropped := [start]) h (by simp)
    simp only [List.length_cons] at this
    omega
  simp only [calldataloadStep, popWord, chargeGas, pushWord, advance, hstack, Stack.pop, Stack.push]
  rcases hc : GasMeter.charge evm.gas OPCODE_CALLDATALOAD with _ | _ <;>
    simp [hc, bind, Except.bind, pure, Except.pure, Except.map, room]

/-- MLOAD on an offset: pay and grow memory, then put the word of memory at the offset in its place.

The word is read after memory has grown. -/
theorem mloadStep_cons {evm : Evm fork Meter} {start : U256} {rest : List U256}
    (h : evm.stack.val = start :: rest) :
    mloadStep evm =
      let growth := extendMemory evm.memory.size [(start, 32)]
      let memory := memoryExtend evm.memory growth.expandBy
      (GasMeter.charge evm.gas (OPCODE_MLOAD_BASE + growth.cost)).map fun gas =>
        { evm with
          stack := ⟨loadWord (memoryReadBytes memory start.toNat 32) 0 32 :: rest,
            length_cons_le (dropped := [start]) h (by simp)⟩,
          gas, memory, pc := evm.pc + 1 } := by
  have hstack : evm.stack = ⟨start :: rest, h ▸ evm.stack.property⟩ := Subtype.ext h
  have room : ¬(rest.length = STACK_LIMIT) := by
    have := length_cons_le (x := start) (dropped := [start]) h (by simp)
    simp only [List.length_cons] at this
    omega
  simp only [mloadStep, popWord, chargeGasAndMemory, chargeGas, pushWord, advance, hstack,
    Stack.pop, Stack.push]
  rcases hc : GasMeter.charge evm.gas
      (OPCODE_MLOAD_BASE + (extendMemory evm.memory.size [(start, 32#256)]).cost) with _ | _ <;>
    simp [hc, bind, Except.bind, pure, Except.pure, Except.map, room]

/-- Each instruction that moves bytes keeps the size of memory a multiple of 32. -/
theorem size_memoryDataStep_mod {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : memoryDataStep op = some step) {evm after : Evm fork Meter}
    (hmod : evm.memory.size % 32 = 0) (h : step evm = .ok after) :
    after.memory.size % 32 = 0 := by
  cases op <;> simp only [memoryDataStep, Option.some.injEq, reduceCtorEq] at hstep <;>
    subst hstep
  case msize | calldatasize | codesize | returndatasize => rwa [memory_readFrame h]
  case mload =>
    obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    simp only [advance, memory_pushWord h3]
    exact size_chargeGasAndMemory_mod (by rw [(popWord_eq_ok h1).2.1]; exact hmod) h2
  case calldataload =>
    obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    simp only [advance, memory_pushWord h3, memory_chargeGas h2, (popWord_eq_ok h1).2.1]
    exact hmod
  case mstore =>
    obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have m2 : e2.memory.size % 32 = 0 := by
      rw [(popWord_eq_ok h2).2.1, (popWord_eq_ok h1).2.1]; exact hmod
    simp only [advance]
    refine size_memoryWrite_chargeGasAndMemory_mod m2 h3 ?_
    exact size_wordBytes _
  case mstore8 =>
    obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have m2 : e2.memory.size % 32 = 0 := by
      rw [(popWord_eq_ok h2).2.1, (popWord_eq_ok h1).2.1]; exact hmod
    simp only [advance]
    refine size_memoryWrite_chargeGasAndMemory_mod m2 h3 ?_
    rfl
  case calldatacopy | codecopy =>
    simp only [copyToMemory] at h
    obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have m3 : e3.memory.size % 32 = 0 := by
      rw [(popWord_eq_ok h3).2.1, (popWord_eq_ok h2).2.1, (popWord_eq_ok h1).2.1]; exact hmod
    simp only [advance]
    refine size_memoryWrite_chargeGasAndMemory_mod m3 h4 ?_
    simp [ByteArray.size, bufferRead_length]
  case mcopy =>
    obtain ⟨⟨dst, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨src, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨length, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have m3 : e3.memory.size % 32 = 0 := by
      rw [(popWord_eq_ok h3).2.1, (popWord_eq_ok h2).2.1, (popWord_eq_ok h1).2.1]; exact hmod
    simp only [advance]
    have fit : (memoryReadBytes e4.memory src.toNat length.toNat).size ≠ 0 →
        dst.toNat + (memoryReadBytes e4.memory src.toNat length.toNat).size ≤
          e4.memory.size := fun hz => by
      have hnz : length ≠ 0 := by
        rintro rfl
        exact hz (by simp [memoryReadBytes])
      have fs := le_size_chargeGasAndMemory m3 h4 (src, length) (by simp) hnz
      have fd := le_size_chargeGasAndMemory m3 h4 (dst, length)
        (List.mem_cons_of_mem _ (by simp)) hnz
      simp only at fs fd
      rw [size_memoryReadBytes fs]
      exact fd
    rw [size_memoryWrite_of_fit fit]
    exact size_chargeGasAndMemory_mod m3 h4
  case returndatacopy =>
    obtain ⟨⟨start, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨offset, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨size, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    have m3 : e3.memory.size % 32 = 0 := by
      rw [(popWord_eq_ok h3).2.1, (popWord_eq_ok h2).2.1, (popWord_eq_ok h1).2.1]; exact hmod
    have m4 := memory_chargeGas h4
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    · rename_i inside
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [advance]
      rw [size_memoryWrite_of_fit fun hz => ?_]
      · rw [m4]
        exact size_memoryExtend_mod m3 _
      · have hnz : size ≠ 0 := by
          rintro rfl
          exact hz (by simp [memoryReadBytes])
        have hcover := le_ceil32_add_expandBy e3.memory.size [(start, size)] (start, size)
          (List.mem_singleton_self _) hnz
        rw [ceil32_of_mod m3] at hcover
        rw [size_memoryReadBytes (Nat.le_of_not_gt inside), size_memoryExtend, m4]
        exact hcover

end EthLib.Execution.Evm
