module

public import EthLib.Execution.Proofs.Evm.Logic.Region

/-!
# Proofs: frames that know a few ranges of memory

A frame of this kind names its memory only by its size and by ranges that hold known bytes.

The rules here give this form to MSTORE, MSTORE8, MCOPY, MLOAD and KECCAK256.

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
  -- Each fact is a start and the bytes that memory holds from there.
  ∀ fact ∈ facts, Holds memory fact.1 fact.2

/-- Whether a fact ends before the range of `length` bytes from `start`, or starts after it. -/
def Apart (start length : Nat) (fact : Nat × ByteArray) : Bool :=
  fact.1 + fact.2.size ≤ start || start + length ≤ fact.1

/-- A fact that ends before a range, or starts after it, is kept by the filter of that range. -/
theorem mem_filter_apart {facts : List (Nat × ByteArray)} {start length : Nat}
    {fact : Nat × ByteArray} (h : fact ∈ facts)
    (hd : fact.1 + fact.2.size ≤ start ∨ start + length ≤ fact.1) :
    fact ∈ facts.filter (Apart start length) :=
  List.mem_filter.mpr ⟨h, by simpa [Apart] using hd⟩

/-- The parts of a fact outside the range of `length` bytes from `start`.

A fact apart from the range stays whole.

A fact that the range overlaps keeps its bytes before the range and its bytes after it. -/
def outside (start length : Nat) (fact : Nat × ByteArray) : List (Nat × ByteArray) :=
  if Apart start length fact then [fact]
  else
    -- The bytes of the fact before the range.
    (if fact.1 < start then [(fact.1, memoryReadBytes fact.2 0 (start - fact.1))] else []) ++
    -- The bytes of the fact after the range.
    (if start + length < fact.1 + fact.2.size then
      [(start + length, memoryReadBytes fact.2 (start + length - fact.1)
        (fact.1 + fact.2.size - (start + length)))]
    else [])

/-- The facts that a write of `length` bytes from `start` keeps: their parts outside the range. -/
def keep (start length : Nat) (facts : List (Nat × ByteArray)) : List (Nat × ByteArray) :=
  facts.flatMap (outside start length)

/-- A fact apart from a range is kept whole by a write to the range. -/
theorem mem_keep_of_mem_filter {facts : List (Nat × ByteArray)} {start length : Nat}
    {fact : Nat × ByteArray} (h : fact ∈ facts.filter (Apart start length)) :
    fact ∈ keep start length facts := by
  obtain ⟨hmem, hapart⟩ := List.mem_filter.mp h
  exact List.mem_flatMap.mpr ⟨fact, hmem, by simp [outside, hapart]⟩

/-- The facts after a write that keeps only the facts apart from it are among those it keeps. -/
theorem sub_keep {facts : List (Nat × ByteArray)} {start length : Nat} (written : Nat × ByteArray) :
    ∀ fact ∈ written :: facts.filter (Apart start length),
      fact ∈ written :: keep start length facts := fun fact hfact => by
  rcases List.mem_cons.mp hfact with rfl | hfact
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (mem_keep_of_mem_filter hfact)

/-- The bytes of the range of `length` bytes from `start`, read along the facts, if they cover it.

Each piece comes from the first fact that holds the first byte of the rest of the range.

A range of no bytes has no reading. -/
def readFacts (facts : List (Nat × ByteArray)) (start length : Nat) : Option ByteArray :=
  if length = 0 then none
  else
    match facts.find? (fun fact => fact.1 ≤ start && start < fact.1 + fact.2.size) with
    | none => none
    | some fact =>
      -- The piece runs to the end of the fact, or to the end of the range.
      let n := min length (fact.1 + fact.2.size - start)
      let piece := memoryReadBytes fact.2 (start - fact.1) n
      if n = length then some piece
      -- The fact holds the first byte, so the piece has some bytes.
      else if n = 0 then none
      else (readFacts facts (start + n) (length - n)).map (piece ++ ·)
termination_by length
decreasing_by omega

/-- A running frame of the code, whose memory has the size `size` and holds the facts.

The size is a multiple of 32. -/
def Known (code : ByteArray) (message : Message fork) (pc : Nat) (stack : List U256)
    (size : Nat) (facts : List (Nat × ByteArray)) (gas : Nat) (state : State.TransactionState)
    (substate : Substate) (returnData : ByteArray) (evm : Evm fork Nat) : Prop :=
  At code message pc stack evm.memory gas state substate returnData evm ∧
    -- The size is a multiple of 32, as every size of memory that the interpreter reaches is.
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

/-- Two facts of adjacent ranges become one fact of the two blocks of bytes, as a step of no opcode.

The second range starts at `mid`, where the first ends. -/
theorem Known.join_step {start mid : Nat} {first second : ByteArray}
    (h₁ : (start, first) ∈ facts) (h₂ : (mid, second) ∈ facts) (hmid : start + first.size = mid) :
    Hoare fork (Known code message pc stack size facts gas state substate returnData)
      (Known code message pc stack size ((start, first ++ second) :: facts) gas state substate
        returnData) :=
  Triple.of_imp fun _ h => h.join h₁ (hmid ▸ h₂)

/-- A frame may forget facts. -/
theorem Known.mono {evm : Evm fork Nat} {fewer : List (Nat × ByteArray)}
    (h : Known code message pc stack size facts gas state substate returnData evm)
    (sub : ∀ fact ∈ fewer, fact ∈ facts) :
    Known code message pc stack size fewer gas state substate returnData evm :=
  ⟨h.1, h.2.1, h.2.2.1, fun fact hfact => h.2.2.2 fact (sub fact hfact)⟩

/-- A frame knows each part of the range of a fact. -/
theorem Known.read {evm : Evm fork Nat} {start offset length : Nat} {bytes : ByteArray}
    (h : Known code message pc stack size facts gas state substate returnData evm)
    (hfact : (start, bytes) ∈ facts) (hfit : offset + length ≤ bytes.size) :
    Known code message pc stack size
      ((start + offset, memoryReadBytes bytes offset length) :: facts) gas state substate
      returnData evm :=
  ⟨h.1, h.2.1, h.2.2.1, fun fact hf => by
    rcases List.mem_cons.mp hf with rfl | hf
    · exact (h.2.2.2 _ hfact).read hfit
    · exact h.2.2.2 fact hf⟩

/-- A write within memory keeps the parts of the facts outside it, and holds what it writes. -/
theorem holdsAll_memoryWrite_keep {memory value : ByteArray} {start : Nat}
    (hw : start + value.size ≤ memory.size) (h : HoldsAll memory facts) :
    HoldsAll (memoryWrite memory start value) ((start, value) :: keep start value.size facts) := by
  intro fact hfact
  rcases List.mem_cons.mp hfact with rfl | hfact
  · exact holds_memoryWrite hw
  obtain ⟨whole, hmem, hpart⟩ := List.mem_flatMap.mp hfact
  have hold := h whole hmem
  have fit := hold.1
  unfold outside at hpart
  split at hpart
  · next hapart =>
    rw [List.mem_singleton.mp hpart]
    simp only [Apart, Bool.or_eq_true, decide_eq_true_eq] at hapart
    exact hold.memoryWrite_of_disjoint hw hapart
  · next hapart =>
    simp only [Apart, Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at hapart
    rcases List.mem_append.mp hpart with hpre | hsuf
    · -- The bytes before the range end where the write starts.
      split at hpre
      · next hlt =>
        rw [List.mem_singleton.mp hpre]
        have hr := hold.read (offset := 0) (length := start - whole.1) (by omega)
        rw [Nat.add_zero] at hr
        exact hr.memoryWrite_of_disjoint hw
          (.inl (by rw [size_memoryReadBytes (by omega)]; omega))
      · cases hpre
    · -- The bytes after the range start where the write ends.
      split at hsuf
      · next hlt =>
        rw [List.mem_singleton.mp hsuf]
        have hr := hold.read (offset := start + value.size - whole.1)
          (length := whole.1 + whole.2.size - (start + value.size)) (by omega)
        rw [show whole.1 + (start + value.size - whole.1) = start + value.size by omega] at hr
        exact hr.memoryWrite_of_disjoint hw (.inr (Nat.le_refl _))
      · cases hsuf

/-- A write within memory keeps the facts apart from it, and holds what it writes. -/
theorem holdsAll_memoryWrite {memory value : ByteArray} {start : Nat}
    (hw : start + value.size ≤ memory.size) (h : HoldsAll memory facts) :
    HoldsAll (memoryWrite memory start value)
      ((start, value) :: facts.filter (Apart start value.size)) := fun fact hfact =>
  holdsAll_memoryWrite_keep hw h fact (sub_keep _ fact hfact)

/-- Facts that cover a range, one after the other, hold the bytes that a read along them gives.

Those bytes have the size of the range. -/
theorem holds_readFacts {memory bytes : ByteArray} {start length : Nat}
    (hall : HoldsAll memory facts) (h : readFacts facts start length = some bytes) :
    Holds memory start bytes ∧ bytes.size = length := by
  induction length using Nat.strongRecOn generalizing start bytes with
  | _ length ih =>
  rw [readFacts] at h
  split at h
  · cases h
  split at h
  · cases h
  · next fact hf =>
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    have hold := hall fact (List.mem_of_find?_eq_some hf)
    -- The piece is the part of the fact from the start of the range.
    have hpiece := hold.read (offset := start - fact.1)
      (length := min length (fact.1 + fact.2.size - start)) (by omega)
    rw [show fact.1 + (start - fact.1) = start by omega] at hpiece
    have hsize := size_memoryReadBytes (memory := fact.2) (start := start - fact.1)
      (size := min length (fact.1 + fact.2.size - start)) (by omega)
    dsimp only at h
    split at h
    · next heq =>
      cases h
      exact ⟨hpiece, by rw [hsize]; exact heq⟩
    split at h
    · cases h
    · next hne _ =>
      cases hr : readFacts facts (start + min length (fact.1 + fact.2.size - start))
        (length - min length (fact.1 + fact.2.size - start)) with
      | none => rw [hr] at h; cases h
      | some rest =>
        rw [hr] at h
        cases h
        obtain ⟨hrest, hrsize⟩ := ih _ (by omega) hr
        refine ⟨hpiece.append (by rw [hsize]; exact hrest), ?_⟩
        rw [ByteArray.size_append, hsize, hrsize]
        omega

/-- A read of a whole block of bytes from its start gives the block. -/
theorem memoryReadBytes_of_size {bytes : ByteArray} {n : Nat} (h : bytes.size = n) :
    memoryReadBytes bytes 0 n = bytes := by
  subst h
  exact memoryReadBytes_whole

/-- The bytes of a word read as that word. -/
theorem loadWord_wordBytes (word : U256) : loadWord (wordBytes word) 0 32 = word := by
  have h := (holds_self (wordBytes word)).loadWord
  rwa [memoryReadBytes_of_size (size_wordBytes word)] at h

/-- The bytes of the word of the first 32 bytes of a block are those bytes. -/
theorem wordBytes_loadWord {b : ByteArray} (h : 32 ≤ b.size) :
    wordBytes (loadWord b 0 32) = memoryReadBytes b 0 32 := by
  have hlen : (bufferRead b 0 32).length = 32 := bufferRead_length b 0 32
  have hnat : (loadWord b 0 32).toNat = EthLib.Base.ByteOrder.ofBE (bufferRead b 0 32) := by
    have h := EthLib.Base.ByteOrder.ofBE_lt (bufferRead b 0 32)
    rw [hlen] at h
    simp only [loadWord, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt h
  have hlist : (U256.toBeBytes (loadWord b 0 32)).toList = bufferRead b 0 32 := by
    rw [U256.toBeBytes, hnat]
    exact EthLib.Base.ByteOrder.toList_toBE_ofBE_of_length hlen
  have hbb : bufferBytes b 0 32 = memoryReadBytes b 0 32 := by
    have hs : (b.extract 0 32).size = 32 := by
      simp only [ByteArray.size_extract]; omega
    unfold bufferBytes memoryReadBytes
    simp only [show 0 < b.size by omega, ↓reduceIte, Nat.zero_add, Nat.min_eq_left h, hs,
      show (32 : Nat) ≠ 0 by decide]
  rw [← hbb, bufferBytes_eq]
  simp only [wordBytes]
  congr 1
  rw [← hlist]
  rfl

/-- A frame knows the bytes that a read along its facts gives, as a fact. -/
theorem Known.readFacts {evm : Evm fork Nat} {start length : Nat} {bytes : ByteArray}
    (h : Known code message pc stack size facts gas state substate returnData evm)
    (hread : readFacts facts start length = some bytes) :
    Known code message pc stack size ((start, bytes) :: facts) gas state substate returnData
      evm :=
  ⟨h.1, h.2.1, h.2.2.1, fun fact hf => by
    rcases List.mem_cons.mp hf with rfl | hf
    · exact (holds_readFacts h.2.2.2 hread).1
    · exact h.2.2.2 fact hf⟩

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
    -- The range has some bytes, since a write of no bytes touches no range.
    {ranges : List (U256 × U256)} {evm : Evm fork Nat} (hz : length ≠ 0)
    (hlen : value.size = length.toNat) (hmem : (start, length) ∈ ranges)
    (hsize : memory.size = size) (hmod : size % 32 = 0) (hall : HoldsAll memory facts)
    (h : At code message pc' stack'
      (memoryWrite (memoryExtend memory (extendMemory size ranges).expandBy) start.toNat value)
      gas' state' substate' returnData evm) :
    -- Memory grows by the growth for the ranges of the write, which depends only on its size.
    Known code message pc' stack' (size + (extendMemory size ranges).expandBy)
      -- The write keeps the parts of each fact outside its range, and adds the fact it writes.
      ((start.toNat, value) :: keep start.toNat length.toNat facts) gas' state'
      substate' returnData evm := by
  have cover := le_ceil32_add_expandBy size ranges (start, length) hmem hz
  rw [ceil32_of_mod hmod] at cover
  have fit : start.toNat + value.size ≤
      (memoryExtend memory (extendMemory size ranges).expandBy).size := by
    rw [size_memoryExtend, hsize, hlen]
    exact cover
  have hm := h.2.2.2.2.2.1
  refine ⟨by rw [hm]; exact h, by rw [hm, size_memoryWrite fit, size_memoryExtend, hsize], ?_,
    by rw [hm, ← hlen]; exact holdsAll_memoryWrite_keep fit (holdsAll_memoryExtend hall _)⟩
  have := size_memoryExtend_mod (memory := memory) (by rw [hsize]; exact hmod) ranges
  rwa [size_memoryExtend, hsize] at this

variable {pc : Nat} {memory : ByteArray}

/-- MSTORE writes the fact of a word, and keeps the parts of the facts outside it.

It pays 3 and the growth of memory, which depends on its size. -/
theorem mstore_known {start value : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x52) (hgas : 3 + (extendMemory size [(start, 32)]).cost ≤ gas) :
    Hoare fork (Known code message pc (start :: value :: rest) size facts gas state substate
        returnData)
      (Known code message (pc + 1) rest (size + (extendMemory size [(start, 32)]).expandBy)
        ((start.toNat, wordBytes value) :: keep start.toNat 32 facts)
        (gas - (3 + (extendMemory size [(start, 32)]).cost)) state substate returnData) := by
  rintro evm ⟨hat, hsize, hmod, hall⟩
  rw [← hsize] at hgas
  obtain ⟨after, hreach, hat'⟩ := mstore hlt hbyte hgas evm hat
  rw [hsize] at hat'
  exact ⟨after, hreach,
    known_of_write (by decide) (size_wordBytes value) (List.mem_singleton_self _)
      hsize hmod hall hat'⟩

/-- MSTORE8 writes the fact of the lowest byte of a word.

It keeps the parts of the facts outside the byte it writes.

It pays 3 and the growth of memory, which depends on its size. -/
theorem mstore8_known {start value : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x53) (hgas : 3 + (extendMemory size [(start, 1)]).cost ≤ gas) :
    Hoare fork (Known code message pc (start :: value :: rest) size facts gas state substate
        returnData)
      (Known code message (pc + 1) rest (size + (extendMemory size [(start, 1)]).expandBy)
        ((start.toNat, ⟨#[UInt8.ofNat value.toNat]⟩) :: keep start.toNat 1 facts)
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

/-- MLOAD of a range that the facts cover pushes the word of the bytes that a read along them gives.

The range may lie within one fact, or run along adjacent facts.

It pays 3, and memory does not grow. -/
theorem mload_known_read {start : U256} {bytes : ByteArray} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x51)
    (hread : readFacts facts start.toNat 32 = some bytes) (hgas : 3 ≤ gas) :
    Hoare fork (Known code message pc (start :: rest) size facts gas state substate returnData)
      (Known code message (pc + 1) (loadWord bytes 0 32 :: rest) size facts (gas - 3) state
        substate returnData) := by
  rintro evm ⟨hat, hsize, hmod, hall⟩
  obtain ⟨hold, hlen⟩ := holds_readFacts hall hread
  have hext : extendMemory evm.memory.size [(start, (32 : U256))] = ⟨0, 0⟩ :=
    extendMemory_of_le (by have := hold.1; rw [hlen] at this; exact this)
  obtain ⟨after, hreach, hat'⟩ := mload (fork := fork) hlt hbyte
    (by rw [hext]; dsimp only; omega) evm hat
  rw [hext] at hat'
  dsimp only at hat'
  have hbytes := hold.2
  rw [hlen] at hbytes
  rw [memoryExtend_zero, hbytes, Nat.add_zero] at hat'
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

/-- From Byzantium, REVERT of no bytes reverts with no output, from any memory, at no price. -/
theorem revert_none (hfork : .byzantium ≤ fork) {start : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xfd) :
    Spec fork (At code message pc (start :: 0 :: rest) memory gas state substate returnData)
      (Halted true .empty gas state substate) := by
  -- A range of no bytes grows no memory and reads no bytes.
  have h := revert (memory := memory) (gas := gas) (start := start) (size := 0) (rest := rest)
    (message := message) (state := state) (substate := substate) (returnData := returnData)
    hfork hlt hbyte (by rw [extendMemory_of_length_eq_zero]; exact Nat.zero_le _)
  rw [extendMemory_of_length_eq_zero] at h
  exact h.consequence (fun _ h => h) fun _ h => by
    simpa [memoryReadBytes] using h

/-- KECCAK256 of the range of a fact pushes the hash of the bytes of the fact.

The hash stays a function of those bytes, so a proof never computes it.

It pays its price on those bytes, and memory does not grow. -/
theorem keccak256_known {start length : U256} {bytes : ByteArray} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x20) (hfact : (start.toNat, bytes) ∈ facts)
    (hlen : bytes.size = length.toNat) (hgas : keccak256Cost length ≤ gas) :
    Hoare fork (Known code message pc (start :: length :: rest) size facts gas state substate
        returnData)
      (Known code message (pc + 1) (keccak bytes :: rest) size facts
        (gas - keccak256Cost length) state substate returnData) := by
  rintro evm ⟨hat, hsize, hmod, hall⟩
  have hold := hall _ hfact
  have hext : extendMemory evm.memory.size [(start, length)] = ⟨0, 0⟩ :=
    extendMemory_of_le (by rw [← hlen]; exact hold.1)
  obtain ⟨after, hreach, hat'⟩ := Logic.keccak256 (fork := fork) hlt hbyte
    (by rw [hext]; dsimp only; omega) evm hat
  rw [hext] at hat'
  dsimp only at hat'
  rw [memoryExtend_zero, ← hlen, hold.2, Nat.add_zero] at hat'
  have hm := hat'.2.2.2.2.2.1
  exact ⟨after, hreach, by rw [hm]; exact hat', by rw [hm]; exact hsize, hmod,
    by rw [hm]; exact hall⟩

/-- KECCAK256 of a range that the facts cover pushes the hash of the bytes read along them.

The range may lie within one fact, or run along adjacent facts.

It pays its price on those bytes, and memory does not grow. -/
theorem keccak256_known_read {start length : U256} {bytes : ByteArray} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x20)
    (hread : readFacts facts start.toNat length.toNat = some bytes)
    (hgas : keccak256Cost length ≤ gas) :
    Hoare fork (Known code message pc (start :: length :: rest) size facts gas state substate
        returnData)
      (Known code message (pc + 1) (keccak bytes :: rest) size facts
        (gas - keccak256Cost length) state substate returnData) := by
  rintro evm hk
  have hk' := hk.readFacts hread
  have hlen := (holds_readFacts hk.2.2.2 hread).2
  obtain ⟨after, hreach, hat', hsize, hmod, hall⟩ :=
    keccak256_known hlt hbyte List.mem_cons_self hlen hgas evm hk'
  -- The fact of the read is dropped again.
  exact ⟨after, hreach, hat', hsize, hmod, fun fact hf => hall fact (List.mem_cons_of_mem _ hf)⟩

/-- The bytes of a read of a buffer have the size of the read. -/
theorem size_bufferRead (data : ByteArray) (offset length : Nat) :
    (⟨(bufferRead data offset length).toArray⟩ : ByteArray).size = length := by
  simp [ByteArray.size, bufferRead_length]

/-- Bytes of one byte have size 1, such as the byte that MSTORE8 writes. -/
theorem size_byte (b : UInt8) : (⟨#[b]⟩ : ByteArray).size = 1 := rfl

/-- From Dencun, MCOPY of the range of a fact writes the fact at the destination.

It keeps the parts of the facts outside the destination.

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
        ((destination.toNat, bytes) :: keep destination.toNat length.toNat facts)
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

/-- From Dencun, MCOPY with both ranges within the range of a fact writes the copy into it.

The source and the destination may overlap: the copy reads the source before it writes.

It keeps the parts of the facts outside the destination.

It pays 3 and 3 gas a word, and memory does not grow. -/
theorem mcopy_known_within (hfork : .dencun ≤ fork) {destination source length : U256}
    {base : Nat} {bytes : ByteArray} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x5e) (hfact : (base, bytes) ∈ facts)
    -- Both ranges lie within the range of the fact.
    (hsource : base ≤ source.toNat) (hsource' : source.toNat + length.toNat ≤ base + bytes.size)
    (hdest : base ≤ destination.toNat)
    (hdest' : destination.toNat + length.toNat ≤ base + bytes.size)
    (hgas : 3 + 3 * wordCount length.toNat ≤ gas) :
    Hoare fork (Known code message pc (destination :: source :: length :: rest) size facts gas
        state substate returnData)
      (Known code message (pc + 1) rest size
        -- The fact holds its bytes with the copy of its source part written at the destination.
        ((base, memoryWrite bytes (destination.toNat - base)
            (memoryReadBytes bytes (source.toNat - base) length.toNat)) ::
          keep destination.toNat length.toNat facts)
        (gas - (3 + 3 * wordCount length.toNat)) state substate returnData) := by
  rintro evm ⟨hat, hsize, hmod, hall⟩
  have hold : Holds evm.memory base bytes := hall _ hfact
  have fit := hold.1
  have hext : extendMemory evm.memory.size [(source, length), (destination, length)] = ⟨0, 0⟩ :=
    extendMemory_eq_zero _ _ fun p hp => .inr <| by
      have hend : p.1.toNat + p.2.toNat ≤ evm.memory.size := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> dsimp only <;> omega
      exact ceil32_le (ceil32_mod _) (Nat.le_trans hend (le_ceil32 _))
  obtain ⟨after, hreach, hat'⟩ := mcopy (fork := fork) hfork hlt hbyte
    (by rw [hext]; dsimp only; omega) evm hat
  rw [hext] at hat'
  dsimp only at hat'
  -- The copy reads the source part of the fact.
  have hpart := hold.read (offset := source.toNat - base) (length := length.toNat) (by omega)
  have hvsize := size_memoryReadBytes (memory := bytes) (start := source.toNat - base)
    (size := length.toNat) (by omega)
  have hread := hpart.2
  rw [hvsize, show base + (source.toNat - base) = source.toNat by omega] at hread
  rw [memoryExtend_zero, hread, Nat.add_zero] at hat'
  have hw : destination.toNat +
      (memoryReadBytes bytes (source.toNat - base) length.toNat).size ≤ evm.memory.size := by
    rw [hvsize]
    omega
  have hm := hat'.2.2.2.2.2.1
  refine ⟨after, hreach, by rw [hm]; exact hat', by rw [hm, size_memoryWrite hw]; exact hsize,
    hmod, ?_⟩
  rw [hm]
  intro fact hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact hold.memoryWrite_within hdest (by rw [hvsize]; exact hdest')
  · rw [← hvsize] at hf
    exact holdsAll_memoryWrite_keep hw hall fact (List.mem_cons_of_mem _ hf)

/-- CALLDATACOPY of a range of some bytes writes the fact of the call data, with zeros past its end.

It keeps the parts of the facts outside the range.

It pays 3, 3 gas a word and the growth of memory, which depends on its size. -/
theorem calldatacopy_known {start offset length : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x37) (hz : length ≠ 0)
    (hgas : 3 + 3 * wordCount length.toNat + (extendMemory size [(start, length)]).cost ≤ gas) :
    Hoare fork (Known code message pc (start :: offset :: length :: rest) size facts gas state
        substate returnData)
      (Known code message (pc + 1) rest (size + (extendMemory size [(start, length)]).expandBy)
        ((start.toNat, ⟨(bufferRead message.data offset.toNat length.toNat).toArray⟩) ::
          keep start.toNat length.toNat facts)
        (gas - (3 + 3 * wordCount length.toNat + (extendMemory size [(start, length)]).cost))
        state substate returnData) := by
  rintro evm ⟨hat, hsize, hmod, hall⟩
  rw [← hsize] at hgas
  obtain ⟨after, hreach, hat'⟩ := calldatacopy hlt hbyte hgas evm hat
  rw [hsize] at hat'
  exact ⟨after, hreach, known_of_write hz (size_bufferRead _ _ _) (List.mem_singleton_self _)
    hsize hmod hall hat'⟩

/-- CODECOPY of a range of some bytes writes the fact of the code, with zeros past its end.

It keeps the parts of the facts outside the range.

It pays 3, 3 gas a word and the growth of memory, which depends on its size. -/
theorem codecopy_known {start offset length : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x39) (hz : length ≠ 0)
    (hgas : 3 + 3 * wordCount length.toNat + (extendMemory size [(start, length)]).cost ≤ gas) :
    Hoare fork (Known code message pc (start :: offset :: length :: rest) size facts gas state
        substate returnData)
      (Known code message (pc + 1) rest (size + (extendMemory size [(start, length)]).expandBy)
        ((start.toNat, ⟨(bufferRead code offset.toNat length.toNat).toArray⟩) ::
          keep start.toNat length.toNat facts)
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
  exact ⟨after, hreach, (known_of_write hz (size_memoryReadBytes fit) (List.mem_singleton_self _)
    hsize hmod hall hat').mono (sub_keep _)⟩

/-- From Berlin to before Glamsterdam, EXTCODECOPY of a range of some bytes writes a fact.

The fact is the code `c` of the account of the address, with zeros past its end.

It keeps the facts apart from the range. -/
theorem extcodecopy_known (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {word start offset length : U256} {rest : List U256} {cold : Bool} {c : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x3c) (hz : length ≠ 0)
    (hcode : state.getCode (state.getAccount (Base.toAddressMasked word)).codeHash = .ok c)
    (hcold : decide (Base.toAddressMasked word ∉ substate.accessedAddresses) = cold)
    -- The copy pays 2600 for a cold address and 100 for a warm one.
    --
    -- It also pays 3 gas a word and the growth of memory.
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
        -- The copy adds the address to the accessed addresses.
        --
        -- It records the read of the account.
        (state.recordAccountRead (Base.toAddressMasked word))
        { substate with
          accessedAddresses :=
            substate.accessedAddresses.insert (Base.toAddressMasked word) } returnData) := by
  rintro evm ⟨hat, hsize, hmod, hall⟩
  rw [← hsize] at hgas
  obtain ⟨after, hreach, hat'⟩ := extcodecopy hfork hglam hlt hbyte hcode hcold hgas evm hat
  rw [hsize] at hat'
  exact ⟨after, hreach, (known_of_write hz (size_bufferRead _ _ _) (List.mem_singleton_self _)
    hsize hmod hall hat').mono (sub_keep _)⟩

end EthLib.Execution.Evm.Logic
