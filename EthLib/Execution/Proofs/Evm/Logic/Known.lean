module

public import EthLib.Execution.Proofs.Evm.Logic.Region

/-!
# Proofs: frames that know a few ranges of memory

A frame of this kind names its memory only by its size and by ranges that hold known bytes.

The size is a multiple of 32, as every size of memory that the interpreter reaches is.

Each fact is a start and the bytes that memory holds from there.

- A rule that keeps memory, for every memory, keeps the size and every fact.
- A write keeps each fact whose range it does not touch, and adds the fact of what it writes.
- Memory grows by the growth for the ranges of the write, which depends only on its size.
- MLOAD of the range of a fact with the bytes of a word pushes that word.
- RETURN and REVERT of the range of a fact give the bytes of the fact.
- Two facts of adjacent ranges join into one, and a frame may forget facts.

The rules here give this form to MSTORE, MSTORE8 and MCOPY.

They give it to CALLDATACOPY, CODECOPY, RETURNDATACOPY and EXTCODECOPY too.

They ask for a range of some bytes, since a write of no bytes touches no range.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork}

/-- Memory holds each range of a list, from its start. -/
def HoldsAll (memory : ByteArray) (facts : List (Nat × ByteArray)) : Prop :=
  ∀ fact ∈ facts, Holds memory fact.1 fact.2

/-- Whether a fact ends before the range of `length` bytes from `start`, or starts after it. -/
def Apart (start length : Nat) (fact : Nat × ByteArray) : Bool :=
  fact.1 + fact.2.size ≤ start || start + length ≤ fact.1

/-- A running frame of the code, whose memory has the size `size` and holds the facts.

The size is a multiple of 32. -/
def Known (code : ByteArray) (message : Message fork) (pc : Nat) (stack : List U256)
    (size : Nat) (facts : List (Nat × ByteArray)) (gas : Nat) (state : State.TransactionState)
    (substate : Substate) (returnData : ByteArray) (evm : Evm fork Nat) : Prop :=
  At code message pc stack evm.memory gas state substate returnData evm ∧
    evm.memory.size = size ∧ size % 32 = 0 ∧ HoldsAll evm.memory facts

variable {code : ByteArray} {message : Message fork} {pc pc' : Nat} {stack stack' : List U256}
  {size : Nat} {facts : List (Nat × ByteArray)} {gas gas' : Nat}
  {state state' : State.TransactionState} {substate substate' : Substate}
  {returnData returnData' : ByteArray}

/-- A frame of empty memory, at the start of a message, knows no fact. -/
theorem known_of_at_empty {evm : Evm fork Nat}
    (h : At code message pc stack .empty gas state substate returnData evm) :
    Known code message pc stack 0 [] gas state substate returnData evm :=
  ⟨by rw [h.2.2.2.2.2.1]; exact h, by rw [h.2.2.2.2.2.1]; rfl, rfl, fun _ hf => by cases hf⟩

/-- Two facts of adjacent ranges give the fact of the two blocks of bytes in order. -/
theorem Known.join {evm : Evm fork Nat} {start : Nat} {first second : ByteArray}
    (h : Known code message pc stack size facts gas state substate returnData evm)
    (h₁ : (start, first) ∈ facts) (h₂ : (start + first.size, second) ∈ facts) :
    Known code message pc stack size ((start, first ++ second) :: facts) gas state substate
      returnData evm :=
  ⟨h.1, h.2.1, h.2.2.1, fun fact hfact => by
    rcases List.mem_cons.mp hfact with rfl | hfact
    · exact (h.2.2.2 _ h₁).append (h.2.2.2 _ h₂)
    · exact h.2.2.2 fact hfact⟩

/-- A frame may forget facts. -/
theorem Known.mono {evm : Evm fork Nat} {fewer : List (Nat × ByteArray)}
    (h : Known code message pc stack size facts gas state substate returnData evm)
    (sub : ∀ fact ∈ fewer, fact ∈ facts) :
    Known code message pc stack size fewer gas state substate returnData evm :=
  ⟨h.1, h.2.1, h.2.2.1, fun fact hfact => h.2.2.2 fact (sub fact hfact)⟩

/-- A write within memory keeps the facts apart from it, and holds what it writes. -/
theorem holdsAll_memoryWrite {memory value : ByteArray} {start : Nat}
    (hw : start + value.size ≤ memory.size) (h : HoldsAll memory facts) :
    HoldsAll (memoryWrite memory start value)
      ((start, value) :: facts.filter (Apart start value.size)) := by
  intro fact hfact
  rcases List.mem_cons.mp hfact with rfl | hfact
  · exact holds_memoryWrite hw
  · obtain ⟨hmem, hapart⟩ := List.mem_filter.mp hfact
    simp only [Apart, Bool.or_eq_true, decide_eq_true_eq] at hapart
    exact (h fact hmem).memoryWrite_of_disjoint hw hapart

/-- Growth keeps every fact. -/
theorem holdsAll_memoryExtend {memory : ByteArray} (h : HoldsAll memory facts) (n : Nat) :
    HoldsAll (memoryExtend memory n) facts :=
  fun fact hfact => (h fact hfact).memoryExtend n

/-- A rule that keeps memory, for every memory, keeps the size and every fact. -/
theorem Known.of_at
    (h : ∀ memory, Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message pc' stack' memory gas' state' substate' returnData')) :
    Hoare fork (Known code message pc stack size facts gas state substate returnData)
      (Known code message pc' stack' size facts gas' state' substate' returnData') := by
  rintro evm ⟨hat, hsize, hmod, hall⟩
  obtain ⟨after, hreach, hat'⟩ := h evm.memory evm hat
  have hm : after.memory = evm.memory := hat'.2.2.2.2.2.1
  exact ⟨after, hreach, by rw [hm]; exact hat', by rw [hm]; exact hsize, hmod,
    by rw [hm]; exact hall⟩

/-- A frame after a write to memory, which grew first for some ranges, is known.

The written range has some bytes and is one of those ranges.

Memory has the size before the growth plus the growth, and holds the facts of the write. -/
theorem known_of_write {memory value : ByteArray} {start length : U256}
    {ranges : List (U256 × U256)} {evm : Evm fork Nat} (hz : length ≠ 0)
    (hlen : value.size = length.toNat) (hmem : (start, length) ∈ ranges)
    (hsize : memory.size = size) (hmod : size % 32 = 0) (hall : HoldsAll memory facts)
    (h : At code message pc' stack'
      (memoryWrite (memoryExtend memory (extendMemory size ranges).expandBy) start.toNat value)
      gas' state' substate' returnData evm) :
    Known code message pc' stack' (size + (extendMemory size ranges).expandBy)
      ((start.toNat, value) :: facts.filter (Apart start.toNat length.toNat)) gas' state'
      substate' returnData evm := by
  have cover := le_ceil32_add_expandBy size ranges (start, length) hmem hz
  rw [ceil32_of_mod hmod] at cover
  have fit : start.toNat + value.size ≤
      (memoryExtend memory (extendMemory size ranges).expandBy).size := by
    rw [size_memoryExtend, hsize, hlen]
    exact cover
  have hm := h.2.2.2.2.2.1
  refine ⟨by rw [hm]; exact h, by rw [hm, size_memoryWrite fit, size_memoryExtend, hsize], ?_,
    by rw [hm, ← hlen]; exact holdsAll_memoryWrite fit (holdsAll_memoryExtend hall _)⟩
  have := size_memoryExtend_mod (memory := memory) (by rw [hsize]; exact hmod) ranges
  rwa [size_memoryExtend, hsize] at this

variable {pc : Nat} {memory : ByteArray}

/-- MSTORE writes the fact of a word, and keeps the facts apart from it.

It pays 3 and the growth of memory, which depends on its size. -/
theorem mstore_known {start value : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x52) (hgas : 3 + (extendMemory size [(start, 32)]).cost ≤ gas) :
    Hoare fork (Known code message pc (start :: value :: rest) size facts gas state substate
        returnData)
      (Known code message (pc + 1) rest (size + (extendMemory size [(start, 32)]).expandBy)
        ((start.toNat, wordBytes value) :: facts.filter (Apart start.toNat 32))
        (gas - (3 + (extendMemory size [(start, 32)]).cost)) state substate returnData) := by
  rintro evm ⟨hat, hsize, hmod, hall⟩
  rw [← hsize] at hgas
  obtain ⟨after, hreach, hat'⟩ := mstore hlt hbyte hgas evm hat
  rw [hsize] at hat'
  exact ⟨after, hreach,
    known_of_write (by decide) (size_wordBytes value) (List.mem_singleton_self _)
      hsize hmod hall hat'⟩

/-- MSTORE8 writes the fact of the lowest byte of a word, and keeps the facts apart from it.

It pays 3 and the growth of memory, which depends on its size. -/
theorem mstore8_known {start value : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x53) (hgas : 3 + (extendMemory size [(start, 1)]).cost ≤ gas) :
    Hoare fork (Known code message pc (start :: value :: rest) size facts gas state substate
        returnData)
      (Known code message (pc + 1) rest (size + (extendMemory size [(start, 1)]).expandBy)
        ((start.toNat, ⟨#[UInt8.ofNat value.toNat]⟩) :: facts.filter (Apart start.toNat 1))
        (gas - (3 + (extendMemory size [(start, 1)]).cost)) state substate returnData) := by
  rintro evm ⟨hat, hsize, hmod, hall⟩
  rw [← hsize] at hgas
  obtain ⟨after, hreach, hat'⟩ := mstore8 hlt hbyte hgas evm hat
  rw [hsize] at hat'
  exact ⟨after, hreach, known_of_write (by decide) rfl (List.mem_singleton_self _) hsize hmod
    hall hat'⟩

/-- MLOAD of the range of a fact with the bytes of a word pushes that word.

It pays 3, and memory does not grow. -/
theorem mload_known {start word : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x51) (hfact : (start.toNat, wordBytes word) ∈ facts)
    (hgas : 3 ≤ gas) :
    Hoare fork (Known code message pc (start :: rest) size facts gas state substate returnData)
      (Known code message (pc + 1) (word :: rest) size facts (gas - 3) state substate
        returnData) := by
  rintro evm ⟨hat, hsize, hmod, hall⟩
  have hold := hall _ hfact
  have hext : extendMemory evm.memory.size [(start, (32 : U256))] = ⟨0, 0⟩ :=
    extendMemory_of_le (by have := hold.1; rw [size_wordBytes] at this; exact this)
  obtain ⟨after, hreach, hat'⟩ := mload (fork := fork) hlt hbyte
    (by rw [hext]; dsimp only; omega) evm hat
  rw [hext] at hat'
  dsimp only at hat'
  rw [memoryExtend_zero, hold.loadWord, Nat.add_zero] at hat'
  have hm := hat'.2.2.2.2.2.1
  exact ⟨after, hreach, by rw [hm]; exact hat', by rw [hm]; exact hsize, hmod,
    by rw [hm]; exact hall⟩

/-- RETURN of the range of a fact stops the frame with the bytes of the fact.

The size of the range is the size of those bytes, and memory does not grow. -/
theorem return_known {start length : U256} {out : ByteArray} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf3) (hfact : (start.toNat, out) ∈ facts)
    (hlen : out.size = length.toNat) :
    Spec fork (Known code message pc (start :: length :: rest) size facts gas state substate
        returnData)
      (Halted false out gas state substate) := by
  rintro evm ⟨hat, hsize, hmod, hall⟩
  have hold := hall _ hfact
  have hext : extendMemory evm.memory.size [(start, length)] = ⟨0, 0⟩ :=
    extendMemory_of_le (by rw [← hlen]; exact hold.1)
  obtain ⟨after, hreach, halted, hq⟩ := «return» (fork := fork) hlt hbyte
    (by rw [hext]; exact Nat.zero_le _) evm hat
  rw [hext] at hq
  dsimp only at hq
  rw [memoryExtend_zero, ← hlen, hold.2, Nat.sub_zero] at hq
  exact ⟨after, hreach, halted, hq⟩

/-- From Byzantium, REVERT of the range of a fact reverts with the bytes of the fact.

The size of the range is the size of those bytes, and memory does not grow. -/
theorem revert_known (hfork : .byzantium ≤ fork) {start length : U256} {out : ByteArray}
    {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0xfd)
    (hfact : (start.toNat, out) ∈ facts) (hlen : out.size = length.toNat) :
    Spec fork (Known code message pc (start :: length :: rest) size facts gas state substate
        returnData)
      (Halted true out gas state substate) := by
  rintro evm ⟨hat, hsize, hmod, hall⟩
  have hold := hall _ hfact
  have hext : extendMemory evm.memory.size [(start, length)] = ⟨0, 0⟩ :=
    extendMemory_of_le (by rw [← hlen]; exact hold.1)
  obtain ⟨after, hreach, halted, hq⟩ := revert (fork := fork) hfork hlt hbyte
    (by rw [hext]; exact Nat.zero_le _) evm hat
  rw [hext] at hq
  dsimp only at hq
  rw [memoryExtend_zero, ← hlen, hold.2, Nat.sub_zero] at hq
  exact ⟨after, hreach, halted, hq⟩

/-- The bytes of a read of a buffer have the size of the read. -/
theorem size_bufferRead (data : ByteArray) (offset length : Nat) :
    (⟨(bufferRead data offset length).toArray⟩ : ByteArray).size = length := by
  simp [ByteArray.size, bufferRead_length]

/-- From Dencun, MCOPY of the range of a fact writes the fact at the destination.

It keeps the facts apart from the destination.

It pays 3, 3 gas a word and the growth of memory for both ranges, which depends on its size. -/
theorem mcopy_known (hfork : .dencun ≤ fork) {destination source length : U256}
    {bytes : ByteArray} {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0x5e)
    (hz : length ≠ 0) (hfact : (source.toNat, bytes) ∈ facts) (hlen : bytes.size = length.toNat)
    (hgas : 3 + 3 * wordCount length.toNat +
      (extendMemory size [(source, length), (destination, length)]).cost ≤ gas) :
    Hoare fork (Known code message pc (destination :: source :: length :: rest) size facts gas
        state substate returnData)
      (Known code message (pc + 1) rest
        (size + (extendMemory size [(source, length), (destination, length)]).expandBy)
        ((destination.toNat, bytes) :: facts.filter (Apart destination.toNat length.toNat))
        (gas - (3 + 3 * wordCount length.toNat +
          (extendMemory size [(source, length), (destination, length)]).cost)) state substate
            returnData) := by
  rintro evm ⟨hat, hsize, hmod, hall⟩
  rw [← hsize] at hgas
  obtain ⟨after, hreach, hat'⟩ := mcopy hfork hlt hbyte hgas evm hat
  have hread : ∀ n, memoryReadBytes (memoryExtend evm.memory n) source.toNat length.toNat =
      bytes := fun n => by
    have := ((hall _ hfact).memoryExtend n).2
    rwa [hlen] at this
  rw [hread, hsize] at hat'
  exact ⟨after, hreach, known_of_write hz hlen (by simp) hsize hmod hall hat'⟩

/-- CALLDATACOPY of a range of some bytes writes the fact of the call data, with zeros past its end.

It keeps the facts apart from the range.

It pays 3, 3 gas a word and the growth of memory, which depends on its size. -/
theorem calldatacopy_known {start offset length : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x37) (hz : length ≠ 0)
    (hgas : 3 + 3 * wordCount length.toNat + (extendMemory size [(start, length)]).cost ≤ gas) :
    Hoare fork (Known code message pc (start :: offset :: length :: rest) size facts gas state
        substate returnData)
      (Known code message (pc + 1) rest (size + (extendMemory size [(start, length)]).expandBy)
        ((start.toNat, ⟨(bufferRead message.data offset.toNat length.toNat).toArray⟩) ::
          facts.filter (Apart start.toNat length.toNat))
        (gas - (3 + 3 * wordCount length.toNat + (extendMemory size [(start, length)]).cost))
        state substate returnData) := by
  rintro evm ⟨hat, hsize, hmod, hall⟩
  rw [← hsize] at hgas
  obtain ⟨after, hreach, hat'⟩ := calldatacopy hlt hbyte hgas evm hat
  rw [hsize] at hat'
  exact ⟨after, hreach, known_of_write hz (size_bufferRead _ _ _) (List.mem_singleton_self _)
    hsize hmod hall hat'⟩

/-- CODECOPY of a range of some bytes writes the fact of the code, with zeros past its end.

It keeps the facts apart from the range.

It pays 3, 3 gas a word and the growth of memory, which depends on its size. -/
theorem codecopy_known {start offset length : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x39) (hz : length ≠ 0)
    (hgas : 3 + 3 * wordCount length.toNat + (extendMemory size [(start, length)]).cost ≤ gas) :
    Hoare fork (Known code message pc (start :: offset :: length :: rest) size facts gas state
        substate returnData)
      (Known code message (pc + 1) rest (size + (extendMemory size [(start, length)]).expandBy)
        ((start.toNat, ⟨(bufferRead code offset.toNat length.toNat).toArray⟩) ::
          facts.filter (Apart start.toNat length.toNat))
        (gas - (3 + 3 * wordCount length.toNat + (extendMemory size [(start, length)]).cost))
        state substate returnData) := by
  rintro evm ⟨hat, hsize, hmod, hall⟩
  rw [← hsize] at hgas
  obtain ⟨after, hreach, hat'⟩ := codecopy hlt hbyte hgas evm hat
  rw [hsize] at hat'
  exact ⟨after, hreach, known_of_write hz (size_bufferRead _ _ _) (List.mem_singleton_self _)
    hsize hmod hall hat'⟩

/-- From Byzantium, RETURNDATACOPY of a range of some bytes writes the fact of the return data.

The range ends within the return data.

It keeps the facts apart from the range, and the return data.

It pays 3, 3 gas a word and the growth of memory, which depends on its size. -/
theorem returndatacopy_known (hfork : .byzantium ≤ fork) {start offset length : U256}
    {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0x3e) (hz : length ≠ 0)
    (fit : offset.toNat + length.toNat ≤ returnData.size)
    (hgas : 3 + 3 * wordCount length.toNat + (extendMemory size [(start, length)]).cost ≤ gas) :
    Hoare fork
      (Known code message pc (start :: offset :: length :: rest) size facts gas state substate
        returnData)
      (Known code message (pc + 1) rest (size + (extendMemory size [(start, length)]).expandBy)
        ((start.toNat, memoryReadBytes returnData offset.toNat length.toNat) ::
          facts.filter (Apart start.toNat length.toNat))
        (gas - (3 + 3 * wordCount length.toNat + (extendMemory size [(start, length)]).cost))
        state substate returnData) := by
  rintro evm ⟨hat, hsize, hmod, hall⟩
  rw [← hsize] at hgas
  obtain ⟨after, hreach, hat'⟩ := returndatacopy hfork hlt hbyte fit hgas evm hat
  rw [hsize] at hat'
  exact ⟨after, hreach, known_of_write hz (size_memoryReadBytes fit) (List.mem_singleton_self _)
    hsize hmod hall hat'⟩

/-- From Berlin to before Glamsterdam, EXTCODECOPY of a range of some bytes writes a fact.

The fact is the code `c` of the account of the address, with zeros past its end.

It keeps the facts apart from the range.

It pays 2600 for a cold address and 100 for a warm one, 3 gas a word and the growth of memory.

It then adds the address to the accessed addresses, and records the read of the account. -/
theorem extcodecopy_known (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {word start offset length : U256} {rest : List U256} {cold : Bool} {c : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x3c) (hz : length ≠ 0)
    (hcode : state.getCode (state.getAccount (Base.toAddressMasked word)).codeHash = .ok c)
    (hcold : decide (Base.toAddressMasked word ∉ substate.accessedAddresses) = cold)
    (hgas : (if cold then 2600 else 100) + 3 * wordCount length.toNat +
      (extendMemory size [(start, length)]).cost ≤ gas) :
    Hoare fork
      (Known code message pc (word :: start :: offset :: length :: rest) size facts gas state
        substate returnData)
      (Known code message (pc + 1) rest (size + (extendMemory size [(start, length)]).expandBy)
        ((start.toNat, ⟨(bufferRead c offset.toNat length.toNat).toArray⟩) ::
          facts.filter (Apart start.toNat length.toNat))
        (gas - ((if cold then 2600 else 100) + 3 * wordCount length.toNat +
          (extendMemory size [(start, length)]).cost))
        (state.recordAccountRead (Base.toAddressMasked word))
        { substate with
          accessedAddresses :=
            substate.accessedAddresses.insert (Base.toAddressMasked word) } returnData) := by
  rintro evm ⟨hat, hsize, hmod, hall⟩
  rw [← hsize] at hgas
  obtain ⟨after, hreach, hat'⟩ := extcodecopy hfork hglam hlt hbyte hcode hcold hgas evm hat
  rw [hsize] at hat'
  exact ⟨after, hreach, known_of_write hz (size_bufferRead _ _ _) (List.mem_singleton_self _)
    hsize hmod hall hat'⟩

end EthLib.Execution.Evm.Logic
