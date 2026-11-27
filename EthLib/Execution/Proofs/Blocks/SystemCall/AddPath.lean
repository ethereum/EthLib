module

public import EthLib.Execution.Proofs.Blocks.SystemCall.RequestQueue

/-!
# Proofs: the add path of a request contract

From byte 143, the codes of EIP-7002 and EIP-7251 store a request and log it.

Their bytes differ only in the number of words of the input, and in its size.

The lemmas here run those bytes once, for any number of words.
-/

@[expose] public section

namespace EthLib.Execution.Blocks.RequestQueue

open EthLib.Base (Fork U256 Address)
open EthLib.Execution.Evm EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Blocks.SystemContract

/-- The words of a request of `n` input words, as the queue holds them.

They are the caller, then the input in words, read big-endian with zeros past its end. -/
def requestWordsOf (n : Nat) (caller : Address) (input : ByteArray) : List U256 :=
  caller.toU256 :: (List.range n).map fun j => loadWord input (32 * j) 32

/-- The data of the log of a request: the 20 bytes of the caller, then the input. -/
def requestLog (caller : Address) (input : ByteArray) : ByteArray :=
  (wordBytes caller.toU256).extract 12 32 ++ input

/-- The 32 bytes from byte 143, with 0 for the number of slots of a request at byte 157.

They count the request, read the tail, store the caller, and store the first word of the input. -/
def ADD_HEAD_NUMBER : Nat :=
  0x600154600101600155600354806000026004013381556001015f358155600101

/-- The 8 bytes that store a word of the input other than the first and the last.

The byte after the first holds the offset of the word in the input, and is 0 here. -/
def ADD_WORD_NUMBER : Nat := 0x6000358155600101

/-- The 5 bytes that store the last word of the input, with 0 for its offset. -/
def ADD_LAST_NUMBER : Nat := 0x6000359055

/-- The 23 bytes that log the request, move the tail and stop.

The bytes 7 and 13 hold the size of the input and the size of the log, and are 0 here. -/
def ADD_LOG_NUMBER : Nat := 0x3360601b5f5260005f60143760005fa060010160035500

/-- The bytes of a code from byte 143 add a request of `n` input words and `size` input bytes.

Each offset of a word is one byte, so `n` is at most 8. -/
structure AddPathCode (code : ByteArray) (n size : Nat) : Prop where
  -- The input has at least two words, and the size of its log fits in one byte.
  two_le : 2 ≤ n
  log_lt : 20 + size < 256
  size_le : 180 + 8 * (n - 2) + 23 ≤ code.size
  -- The first 32 bytes, with the number of slots of a request, one more than the words.
  head : ∀ i (h : i < code.size), 143 ≤ i → i < 175 → i ≠ 157 →
    code[i] = NatCode.natByte ADD_HEAD_NUMBER 32 (i - 143)
  push156 : pushData code 156 1 = BitVec.ofNat 256 (n + 1)
  -- The words 1 to `n - 2`, the word `j` from byte `175 + 8 * (j - 1)`, at offset `32 * j`.
  word : ∀ j, 1 ≤ j → j + 2 ≤ n → ∀ i (h : 175 + 8 * (j - 1) + i < code.size), i < 8 → i ≠ 1 →
    code[175 + 8 * (j - 1) + i] = NatCode.natByte ADD_WORD_NUMBER 8 i
  pushWord : ∀ j, 1 ≤ j → j + 2 ≤ n →
    pushData code (175 + 8 * (j - 1)) 1 = BitVec.ofNat 256 (32 * j)
  -- The last word, from byte `175 + 8 * (n - 2)`.
  last : ∀ i (h : 175 + 8 * (n - 2) + i < code.size), i < 5 → i ≠ 1 →
    code[175 + 8 * (n - 2) + i] = NatCode.natByte ADD_LAST_NUMBER 5 i
  pushLast : pushData code (175 + 8 * (n - 2)) 1 = BitVec.ofNat 256 (32 * (n - 1))
  -- The log, from byte `180 + 8 * (n - 2)`, with the size of the input and of the log.
  log : ∀ i (h : 180 + 8 * (n - 2) + i < code.size), i < 23 → i ≠ 7 → i ≠ 13 →
    code[180 + 8 * (n - 2) + i] = NatCode.natByte ADD_LOG_NUMBER 23 i
  pushSize : pushData code (180 + 8 * (n - 2) + 6) 1 = BitVec.ofNat 256 size
  pushLog : pushData code (180 + 8 * (n - 2) + 12) 1 = BitVec.ofNat 256 (20 + size)

namespace AddPathCode

variable {code : ByteArray} {n size : Nat} {fork : Fork} {message : Message fork}
  {returnData : ByteArray}

/-- The storage after the count and the first `k` words of a request are stored, from `read`. -/
def addedPrefix (slots : Nat) (words : List U256) (read : U256 → U256) (k : Nat) :
    U256 → U256 :=
  (words.take k).zipIdx.foldl
    (fun r (word, j) => setSlot r (4 + read 3 * BitVec.ofNat 256 slots + BitVec.ofNat 256 j) word)
    (setSlot read 1 (read 1 + 1))

/-- Before any word, the storage holds the count of the block, one more. -/
theorem addedPrefix_zero (slots : Nat) (words : List U256) (read : U256 → U256) :
    addedPrefix slots words read 0 = setSlot read 1 (read 1 + 1) := rfl

/-- The word `k` of a request goes to the slot `k` after the start of the request. -/
theorem addedPrefix_succ {slots : Nat} {words : List U256} {read : U256 → U256} {k : Nat}
    (hk : k < words.length) :
    addedPrefix slots words read (k + 1) = setSlot (addedPrefix slots words read k)
      (4 + read 3 * BitVec.ofNat 256 slots + BitVec.ofNat 256 k) words[k] := by
  simp only [addedPrefix]
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.zipIdx_append,
    List.foldl_append]
  simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]

/-- With every word stored, the tail grows by one, and the request is added. -/
theorem afterAdd_eq (slots : Nat) (words : List U256) (read : U256 → U256) :
    afterAdd slots words read =
      setSlot (addedPrefix slots words read words.length) 3 (read 3 + 1) := by
  simp [afterAdd, addedPrefix]

/-- A request of `n` input words has `n + 1` words. -/
theorem length_requestWordsOf (n : Nat) (caller : Address) (input : ByteArray) :
    (requestWordsOf n caller input).length = n + 1 := by
  simp [requestWordsOf]

/-- The first word of a request is the caller. -/
theorem getElem_requestWordsOf_zero {n : Nat} {caller : Address} {input : ByteArray}
    (h : 0 < (requestWordsOf n caller input).length) :
    (requestWordsOf n caller input)[0] = caller.toU256 := by
  simp [requestWordsOf]

/-- The word `j + 1` of a request is the word `j` of the input. -/
theorem getElem_requestWordsOf_succ {n j : Nat} {caller : Address} {input : ByteArray}
    (h : j + 1 < (requestWordsOf n caller input).length) :
    (requestWordsOf n caller input)[j + 1] = loadWord input (32 * j) 32 := by
  simp [requestWordsOf]

/-- The word `k` of a request, after the first, is the word `k - 1` of the input. -/
theorem getElem_requestWordsOf_pos {n k : Nat} {caller : Address} {input : ByteArray}
    (hk : 0 < k) (h : k < (requestWordsOf n caller input).length) :
    (requestWordsOf n caller input)[k] = loadWord input (32 * (k - 1)) 32 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact getElem_requestWordsOf_succ h

/-- A copy of `size` bytes to offset 20 of 32 bytes of memory costs at most 30 gas.

Memory is then large enough for the copy. -/
private theorem extendMemory_copy {size : Nat} (hs : 20 + size < 256) :
    (extendMemory 32 [(20#256, BitVec.ofNat 256 size)]).cost ≤ 30 ∧
      20 + size ≤ 32 + (extendMemory 32 [(20#256, BitVec.ofNat 256 size)]).expandBy := by
  have hsize : (BitVec.ofNat 256 size).toNat = size := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases h : 32 < 20 + size
  · have hz : BitVec.ofNat 256 size ≠ 0 := by
      intro e
      have := congrArg BitVec.toNat e
      rw [hsize] at this
      simp at this
      omega
    rw [extendMemory_of_lt (by decide) hz (by rw [hsize]; simpa using h)]
    rw [hsize, show (20#256 : U256).toNat = 20 from rfl]
    have hc := ceil32_le (value := 20 + size) (bound := 256) (by decide) (by omega)
    have hl := le_ceil32 (20 + size)
    have hw : wordCount (ceil32 (20 + size)) ≤ 8 := wordCount_le (by omega)
    have hsq := Nat.pow_le_pow_left hw 2
    simp only [memoryGasCost, GasCosts.MEMORY_PER_WORD]
    omega
  · rw [extendMemory_of_le (by rw [hsize]; simp; omega)]
    simp
    omega

/-- The data of a PUSH1 inside the code is the byte after it. -/
theorem pushData_one {code : ByteArray} {pc : Nat} (h : pc + 1 < code.size) :
    pushData code pc 1 = BitVec.ofNat 256 (code[pc + 1]).toNat := by
  unfold pushData
  rw [bufferRead_eq]
  simp [EthLib.Base.byteAtOrZero, h, EthLib.Base.ByteOrder.ofBE, EthLib.Base.ByteOrder.ofBE.go,
    EthLib.Base.ByteOrder.ofBE.horner]

/-- The data of a PUSH1 is below 256. -/
theorem toNat_pushData_one_lt (code : ByteArray) (pc : Nat) :
    (pushData code pc 1).toNat < 256 := by
  unfold pushData
  rw [bufferRead_eq]
  simp only [List.range_one, List.map_cons, List.map_nil, EthLib.Base.ByteOrder.ofBE,
    EthLib.Base.ByteOrder.ofBE.go, EthLib.Base.ByteOrder.ofBE.horner, BitVec.toNat_ofNat]
  simp
  have := (EthLib.Base.byteAtOrZero code (pc + 1)).toNat_lt
  omega

/-- A request has at most eight input words, since the offset of each word fits in a byte. -/
theorem le_eight (hc : AddPathCode code n size) : n ≤ 8 := by
  -- From ten words on, the word 8 is a middle word, whose offset 256 is no byte.
  have h9 : n ≤ 9 := by
    refine Nat.le_of_not_lt fun h => ?_
    have h8 := hc.pushWord 8 (by decide) (by omega)
    have := toNat_pushData_one_lt code (175 + 8 * (8 - 1))
    rw [h8] at this
    simp at this
  -- At nine words, the last word has that offset.
  have := toNat_pushData_one_lt code (175 + 8 * (n - 2))
  rw [hc.pushLast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
  omega

set_option hygiene false in
/-- Runs one step of the first 32 bytes, from the facts of the code. -/
local macro "head_step" : tactic => `(tactic| evm_step [hc.head, hl, pushData_one, ne_eq,
  Nat.reduceEqDiff, Nat.reduceLeDiff, not_false_eq_true, ADD_HEAD_NUMBER])

set_option hygiene false in
/-- Runs the PUSH1 of the number of slots of a request, at byte 156. -/
local macro "slots_step" : tactic => `(tactic| evm_step [hc.head, hl, hc.push156, ne_eq,
  Nat.reduceEqDiff, Nat.reduceLeDiff, not_false_eq_true, ADD_HEAD_NUMBER])

set_option hygiene false in
/-- Proves a fact about a byte of the first 32 bytes, from the facts of the code. -/
local macro "head_code" : tactic => `(tactic| evm_code [hc.head, hl, ne_eq, Nat.reduceEqDiff,
  Nat.reduceLeDiff, not_false_eq_true, ADD_HEAD_NUMBER])

/-- From byte 143, the code counts the request, stores the caller and the first word of the input.

It reaches byte 175 with the slot of the next word and the tail.

It spends at most 72,200 gas, five times that from Glamsterdam. -/
theorem head_then (hc : AddPathCode code n size) {S : TransactionState} {ss : Substate}
    {g : Nat} {Q : Evm fork Nat → Prop}
    (hfork : .shapella ≤ fork) (hstatic : message.isStatic = false)
    (hacc : (S.getAccountOptional message.currentTarget).isSome = true)
    (hgas : 100000 * storageGasScale fork ≤ g)
    (next : ∀ S' g' ss', WritesStorage message.currentTarget
        (addedPrefix (n + 1) (requestWordsOf n message.caller message.data)
          (storageOf S message.currentTarget) 2) S S' →
      (S'.getAccountOptional message.currentTarget).isSome = true →
      g ≤ g' + 72200 * storageGasScale fork → ss'.logs = ss.logs →
      Spec fork (At code message 175
        [4 + storageOf S message.currentTarget 3 * BitVec.ofNat 256 (n + 1) + BitVec.ofNat 256 2,
          storageOf S message.currentTarget 3] .empty g' S' ss' returnData) Q) :
    Spec fork (At code message 143 [] .empty g S ss returnData) Q := by
  have hscale := one_le_storageGasScale fork
  have hl : ∀ i, i < 203 → i < code.size := fun i h => by have := hc.size_le; omega
  head_step
  refine sload_then (Nat.le_trans (by decide) hfork) (by head_code) (by head_code) (by omega)
    fun g0 ss0 hg0 hl0 => ?_
  head_step
  head_step
  head_step
  refine sstore_then (Nat.le_trans (by decide) hfork) (by head_code) (by head_code) hstatic hacc
    (by omega) fun S1 hw1 hacc1 g1 ss1 hg1 hl1 => ?_
  have hw1 := WritesStorage.trans (WritesStorage.recordStorageRead _ _ _ _) hw1
  head_step
  refine sload_then (Nat.le_trans (by decide) hfork) (by head_code) (by head_code) (by omega)
    fun g2 ss2 hg2 hl2 => ?_
  have h3 : storageOf S1 message.currentTarget 3#256 = storageOf S message.currentTarget 3#256 := by
    rw [hw1.1]
    simp only [setSlot]
    rfl
  rw [h3]
  have hw2 := WritesStorage.trans hw1
    (WritesStorage.recordStorageRead _ S1 message.currentTarget (U256.toBeBytes 3#256))
  have e3 : storageOf S message.currentTarget 3 = storageOf S message.currentTarget 3#256 := rfl
  rw [e3] at next
  generalize ht : storageOf S message.currentTarget 3#256 = t at hw2 next ⊢
  head_step
  slots_step
  head_step
  head_step
  head_step
  head_step
  head_step
  refine sstore_then (Nat.le_trans (by decide) hfork) (by head_code) (by head_code) hstatic hacc1
    (by omega) fun S3 hw3 hacc3 g3 ss3 hg3 hl3 => ?_
  have hw3 := WritesStorage.trans hw2 hw3
  head_step
  head_step
  head_step
  head_step
  head_step
  refine sstore_then (Nat.le_trans (by decide) hfork) (by head_code) (by head_code) hstatic hacc3
    (by omega) fun S4 hw4 hacc4 g4 ss4 hg4 hl4 => ?_
  have hw4 := WritesStorage.trans hw3 hw4
  head_step
  head_step
  have hp : add 1#256 (add 1#256 (add 4#256 (mul (BitVec.ofNat 256 (n + 1)) t))) =
      4 + t * BitVec.ofNat 256 (n + 1) + BitVec.ofNat 256 2 := by
    simp only [add, mul]
    rw [BitVec.mul_comm]
    generalize t * BitVec.ofNat 256 (n + 1) = m
    bv_omega
  rw [hp]
  refine next S4 (g4 - 6) ss4 ⟨fun slot => ?_, hw4.2.1, hw4.2.2.1, hw4.2.2.2⟩ hacc4 (by omega)
    (by rw [hl4, hl3, hl2, hl1, hl0])
  have hn := hc.two_le
  have e3 := funext hw3.1
  have e1 := funext hw1.1
  rw [hw4.1, e3]
  change setSlot (setSlot (storageOf S1 message.currentTarget) _ _) _ _ slot = _
  rw [e1, addedPrefix_succ (by simp only [length_requestWordsOf]; omega),
    addedPrefix_succ (by simp only [length_requestWordsOf]; omega), addedPrefix_zero,
    getElem_requestWordsOf_zero, getElem_requestWordsOf_succ, ← ht]
  refine congrFun (setSlot_congr (setSlot_congr (setSlot_congr rfl rfl ?_) ?_ rfl) ?_
    (by rw [Nat.mul_zero])) slot <;>
    simp only [add, mul, BitVec.mul_comm (BitVec.ofNat 256 (n + 1))] <;>
    generalize storageOf S message.currentTarget 3#256 * BitVec.ofNat 256 (n + 1) = m <;>
    bv_omega

set_option hygiene false in
/-- Runs one step of the block of a word, from the facts of the code. -/
local macro "word_step" : tactic => `(tactic| evm_step [hw, hl, pushData_one, ne_eq,
  Nat.reduceEqDiff, not_false_eq_true, ADD_WORD_NUMBER, Nat.add_assoc])

set_option hygiene false in
/-- Runs the PUSH1 of the offset of a word, the first step of its block. -/
local macro "offset_step" : tactic => `(tactic| evm_step [hw, hl, hpw, ne_eq,
  Nat.reduceEqDiff, not_false_eq_true, ADD_WORD_NUMBER, Nat.add_assoc])

set_option hygiene false in
/-- Proves a fact about a byte of the block of a word, from the facts of the code. -/
local macro "word_code" : tactic => `(tactic| evm_code [hw, hl, ne_eq, Nat.reduceEqDiff,
  not_false_eq_true, ADD_WORD_NUMBER, Nat.add_assoc])

/-- From byte `175 + 8 * (j - 1)`, the code stores the word `j` of the input.

It goes to the slot `j + 1` of the request.

It reaches the block of the next word, for at most 22,200 gas, five times that from Glamsterdam. -/
theorem word_then (hc : AddPathCode code n size) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j + 2 ≤ n)
    {S S' : TransactionState} {ss ss' : Substate} {g g' : Nat} {Q : Evm fork Nat → Prop}
    (hfork : .shapella ≤ fork) (hstatic : message.isStatic = false)
    (hgas : 25000 * storageGasScale fork * (n + 4) ≤ g)
    (hw' : WritesStorage message.currentTarget
      (addedPrefix (n + 1) (requestWordsOf n message.caller message.data)
        (storageOf S message.currentTarget) (j + 1)) S S')
    (hacc : (S'.getAccountOptional message.currentTarget).isSome = true)
    (hg : g ≤ g' + storageGasScale fork * (50000 + 22200 * j)) (hlogs : ss'.logs = ss.logs)
    (next : ∀ S'' g'' ss'', WritesStorage message.currentTarget
        (addedPrefix (n + 1) (requestWordsOf n message.caller message.data)
          (storageOf S message.currentTarget) (j + 2)) S S'' →
      (S''.getAccountOptional message.currentTarget).isSome = true →
      g ≤ g'' + storageGasScale fork * (50000 + 22200 * (j + 1)) → ss''.logs = ss.logs →
      Spec fork (At code message (175 + 8 * j)
        [4 + storageOf S message.currentTarget 3 * BitVec.ofNat 256 (n + 1) +
          BitVec.ofNat 256 (j + 2), storageOf S message.currentTarget 3] .empty g'' S'' ss''
          returnData) Q) :
    Spec fork (At code message (175 + 8 * (j - 1))
      [4 + storageOf S message.currentTarget 3 * BitVec.ofNat 256 (n + 1) +
        BitVec.ofNat 256 (j + 1), storageOf S message.currentTarget 3] .empty g' S' ss'
        returnData) Q := by
  have hscale := one_le_storageGasScale fork
  -- The words left after this one pay for its write.
  have hA : storageGasScale fork * (50000 + 22200 * j) + 100000 * storageGasScale fork ≤
      25000 * storageGasScale fork * (n + 4) := by
    rw [Nat.mul_comm 25000, Nat.mul_assoc, Nat.mul_comm 100000, ← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (by omega)
  have hB : storageGasScale fork * (50000 + 22200 * (j + 1)) =
      storageGasScale fork * (50000 + 22200 * j) + 22200 * storageGasScale fork := by
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  have h9 := hc.le_eight
  have hw := hc.word j hj1 hj2
  have hpw : pushData code (175 + 8 * (j - 1) + 0) 1 = BitVec.ofNat 256 (32 * j) :=
    hc.pushWord j hj1 hj2
  have hl : ∀ i, i < 8 → 175 + 8 * (j - 1) + i < code.size := fun i h => by
    have := hc.size_le
    omega
  have h32 : (BitVec.ofNat 256 (32 * j)).toNat = 32 * j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [show 175 + 8 * j = 175 + 8 * (j - 1) + 8 by omega] at next
  generalize 175 + 8 * (j - 1) = o at hw hpw hl next ⊢
  rw [← Nat.add_zero o]
  offset_step
  word_step
  rw [show pushData code (o + 0) 1 = BitVec.ofNat 256 (32 * j) from hpw, h32]
  word_step
  refine sstore_then (Nat.le_trans (by decide) hfork) (by word_code) (by word_code) hstatic hacc
    (by omega) fun S1 hw1 hacc1 g1 ss1 hg1 hl1 => ?_
  word_step
  word_step
  have hp : add 1#256 (4 + storageOf S message.currentTarget 3 * BitVec.ofNat 256 (n + 1) +
      BitVec.ofNat 256 (j + 1)) = 4 + storageOf S message.currentTarget 3 *
        BitVec.ofNat 256 (n + 1) + BitVec.ofNat 256 (j + 2) := by
    simp only [add]
    generalize 4 + storageOf S message.currentTarget 3 * BitVec.ofNat 256 (n + 1) = A
    bv_omega
  rw [hp]
  refine next S1 (g1 - 6) ss1 ?_ hacc1 (by omega) (by rw [hl1, hlogs])
  rw [funext hw'.1] at hw1
  rw [addedPrefix_succ (by simp only [length_requestWordsOf]; omega),
    getElem_requestWordsOf_succ]
  exact WritesStorage.trans hw' hw1

set_option hygiene false in
/-- Runs one step of the block of the last word, from the facts of the code. -/
local macro "last_step" : tactic => `(tactic| evm_step [hw, hl, hpw, ne_eq,
  Nat.reduceEqDiff, not_false_eq_true, ADD_LAST_NUMBER, Nat.add_assoc])

set_option hygiene false in
/-- Proves a fact about a byte of the block of the last word, from the facts of the code. -/
local macro "last_code" : tactic => `(tactic| evm_code [hw, hl, ne_eq, Nat.reduceEqDiff,
  not_false_eq_true, ADD_LAST_NUMBER, Nat.add_assoc])

set_option hygiene false in
/-- Runs one step of the block of the log, from the facts of the code. -/
local macro "log_step" : tactic => `(tactic| evm_step [hlg, hl2, pushData_one, ne_eq,
  Nat.reduceEqDiff, not_false_eq_true, ADD_LOG_NUMBER, Nat.add_assoc])

set_option hygiene false in
/-- Runs the PUSH1 of a size in the block of the log. -/
local macro "size_step" : tactic => `(tactic| evm_step [hlg, hl2, hps, hpl, ne_eq,
  Nat.reduceEqDiff, not_false_eq_true, ADD_LOG_NUMBER, Nat.add_assoc])

set_option hygiene false in
/-- Proves a fact about a byte of the block of the log, from the facts of the code. -/
local macro "log_code" : tactic => `(tactic| evm_code [hlg, hl2, ne_eq, Nat.reduceEqDiff,
  not_false_eq_true, ADD_LOG_NUMBER, Nat.add_assoc])

/-- From byte `175 + 8 * (n - 2)`, the code stores the last word, logs the request and stops.

The tail grows by one, and the request is added. -/
theorem last_then (hc : AddPathCode code n size) {S S' : TransactionState} {ss ss' : Substate}
    {g g' : Nat} (hfork : .shapella ≤ fork)
    (hstatic : message.isStatic = false) (hsize : message.data.size = size)
    (hgas : 25000 * storageGasScale fork * (n + 4) ≤ g)
    (hw' : WritesStorage message.currentTarget
      (addedPrefix (n + 1) (requestWordsOf n message.caller message.data)
        (storageOf S message.currentTarget) n) S S')
    (hacc : (S'.getAccountOptional message.currentTarget).isSome = true)
    (hg : g ≤ g' + storageGasScale fork * (50000 + 22200 * (n - 1)))
    (hlogs : ss'.logs = ss.logs) :
    Spec fork (At code message (175 + 8 * (n - 2))
      [4 + storageOf S message.currentTarget 3 * BitVec.ofNat 256 (n + 1) + BitVec.ofNat 256 n,
        storageOf S message.currentTarget 3] .empty g' S' ss' returnData) fun evm =>
      Added (n + 1) message.currentTarget (requestWordsOf n message.caller message.data)
        (requestLog message.caller message.data) S ss evm ∧
      g ≤ evm.gas + 25000 * storageGasScale fork * (n + 4) := by
  have hscale := one_le_storageGasScale fork
  have h9 := hc.le_eight
  have h2 := hc.two_le
  -- The budget left pays for the two writes and the log.
  have hA : storageGasScale fork * (50000 + 22200 * (n - 1)) + 72200 * storageGasScale fork ≤
      25000 * storageGasScale fork * (n + 4) := by
    rw [Nat.mul_comm 25000, Nat.mul_assoc, Nat.mul_comm 72200, ← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (by omega)
  have hls := hc.log_lt
  have hw := hc.last
  have hpw : pushData code (175 + 8 * (n - 2) + 0) 1 = BitVec.ofNat 256 (32 * (n - 1)) :=
    hc.pushLast
  have hlg := hc.log
  have hps := hc.pushSize
  have hpl := hc.pushLog
  have hl : ∀ i, i < 5 → 175 + 8 * (n - 2) + i < code.size := fun i h => by
    have := hc.size_le
    omega
  have hl2 : ∀ i, i < 23 → 180 + 8 * (n - 2) + i < code.size := fun i h => by
    have := hc.size_le
    omega
  have h32 : (BitVec.ofNat 256 (32 * (n - 1))).toNat = 32 * (n - 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have ho : 175 + 8 * (n - 2) + 5 = 180 + 8 * (n - 2) + 0 := by omega
  generalize 180 + 8 * (n - 2) = o2 at hlg hps hpl hl2 ho
  generalize 175 + 8 * (n - 2) = o at hw hpw hl ho ⊢
  rw [← Nat.add_zero o]
  last_step
  last_step
  rw [show pushData code (o + 0) 1 = BitVec.ofNat 256 (32 * (n - 1)) from hpw, h32]
  last_step
  refine sstore_then (Nat.le_trans (by decide) hfork) (by last_code) (by last_code) hstatic hacc
    (by omega) fun S1 hw1 hacc1 g1 ss1 hg1 hl1 => ?_
  rw [ho, ← Nat.add_zero o2]
  log_step
  log_step
  log_step
  log_step
  refine Triple.seq (mstore (by log_code) (by log_code)
    (by simp only [ByteArray.size_empty, extendMemory_word]; omega)) ?_
  rw [ByteArray.size_empty, extendMemory_word]
  dsimp only
  rw [show BitVec.toNat (0 : U256) = 0 from rfl,
    memoryWrite_whole (by rw [size_memoryExtend, size_wordBytes]; rfl)]
  simp only [At.pc_add_add, Nat.reduceAdd]
  size_step
  log_step
  log_step
  obtain ⟨hcost, hfit⟩ := extendMemory_copy hls
  have hwc : wordCount (BitVec.ofNat 256 size).toNat ≤ 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact wordCount_le (by omega)
  refine Triple.seq (calldatacopy (by log_code) (by log_code)
    (by rw [size_wordBytes]; omega)) ?_
  rw [size_wordBytes]
  have hsz : (BitVec.ofNat 256 size).toNat = size := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsz2 : (BitVec.ofNat 256 (20 + size)).toNat = 20 + size := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  generalize hG : g1 - 24 - (3 + 3 * wordCount (BitVec.ofNat 256 size).toNat +
    (extendMemory 32 [(20#256, BitVec.ofNat 256 size)]).cost) = G
  have hG' : g1 - 24 - 60 ≤ G := by omega
  clear hG hcost hwc
  generalize (extendMemory 32 [(20#256, BitVec.ofNat 256 size)]).expandBy = e at hfit ⊢
  rw [hsz, show (20#256 : U256).toNat = 20 from rfl, show BitVec.toNat (0 : U256) = 0 from rfl]
  have hM := log_memory (c := message.caller.toU256) hsize hfit
  have hMs : (memoryWrite (memoryExtend (wordBytes (bitwiseShl 96#256 message.caller.toU256)) e)
      20 ⟨(bufferRead message.data 0 size).toArray⟩).size = 32 + e := by
    have hb : (⟨(bufferRead message.data 0 size).toArray⟩ : ByteArray).size = size := by
      show (bufferRead _ _ _).toArray.size = size
      rw [List.size_toArray, bufferRead_length]
    rw [size_memoryWrite (by rw [hb, size_memoryExtend, size_wordBytes]; omega),
      size_memoryExtend, size_wordBytes]
  generalize memoryWrite (memoryExtend (wordBytes (bitwiseShl 96#256 message.caller.toU256)) e)
    20 ⟨(bufferRead message.data 0 size).toArray⟩ = M at hM hMs ⊢
  simp only [At.pc_add_add, Nat.reduceAdd]
  size_step
  log_step
  have hle : extendMemory M.size [((0 : U256), BitVec.ofNat 256 (20 + size))] = ⟨0, 0⟩ :=
    extendMemory_of_le (by rw [hMs, hsz2]; simp; omega)
  refine Triple.seq (Logic.log (n := 0) (words := [])
    (rest := [storageOf S message.currentTarget 3]) rfl (by log_code) (by log_code) (by decide)
    hstatic (by
      rw [hle]
      simp only [logCost, GasCosts.OPCODE_LOG_BASE, GasCosts.OPCODE_LOG_DATA_PER_BYTE,
        GasCosts.OPCODE_LOG_TOPIC, hsz2]
      omega)) ?_
  rw [hle]
  dsimp only
  rw [memoryExtend_zero]
  have hM' : memoryReadBytes M 0 (20 + size) = requestLog message.caller message.data := hM
  simp only [hsz2, show BitVec.toNat (0 : U256) = 0 from rfl, List.map_nil, hM', logCost,
    GasCosts.OPCODE_LOG_BASE, GasCosts.OPCODE_LOG_DATA_PER_BYTE, GasCosts.OPCODE_LOG_TOPIC,
    Nat.add_zero, Fin.val_zero, Nat.mul_zero, At.pc_add_add, Nat.reduceAdd]
  clear hM hM' hle hMs
  log_step
  log_step
  log_step
  refine sstore_then (Nat.le_trans (by decide) hfork) (by log_code) (by log_code) hstatic hacc1
    (by omega) fun S2 hw2 _ g2 ss2 hg2 hlog2 => ?_
  refine Spec.consequence (stop (by log_code) (by log_code)) (fun _ h => h) ?_
  rintro evm ⟨-, herr, hout, hgas', hst, hss⟩
  refine ⟨⟨by simpa using herr, hout, ?_, ?_⟩, by omega⟩
  · rw [hst]
    rw [funext hw'.1] at hw1
    rw [funext hw1.1] at hw2
    have hw := WritesStorage.trans (WritesStorage.trans hw' hw1) hw2
    rw [afterAdd_eq, length_requestWordsOf,
      addedPrefix_succ (by simp only [length_requestWordsOf]; omega),
      getElem_requestWordsOf_pos (by omega)]
    rw [show add 1#256 (storageOf S message.currentTarget 3) =
      storageOf S message.currentTarget 3 + 1 from BitVec.add_comm _ _] at hw
    exact hw
  · rw [hss, hlog2]
    simp only [hl1, hlogs]

/-- From the block of the word `j`, the code adds the request.

`k` middle words are left, the word `j` included. -/
theorem words_then (hc : AddPathCode code n size) {S : TransactionState} {ss : Substate}
    {g : Nat} (hfork : .shapella ≤ fork)
    (hstatic : message.isStatic = false) (hsize : message.data.size = size)
    (hgas : 25000 * storageGasScale fork * (n + 4) ≤ g) (k : Nat) :
    ∀ j, j + k + 1 = n → 1 ≤ j → ∀ S' g' ss', WritesStorage message.currentTarget
      (addedPrefix (n + 1) (requestWordsOf n message.caller message.data)
        (storageOf S message.currentTarget) (j + 1)) S S' →
      (S'.getAccountOptional message.currentTarget).isSome = true →
      g ≤ g' + storageGasScale fork * (50000 + 22200 * j) → ss'.logs = ss.logs →
      Spec fork (At code message (175 + 8 * (j - 1))
        [4 + storageOf S message.currentTarget 3 * BitVec.ofNat 256 (n + 1) +
          BitVec.ofNat 256 (j + 1), storageOf S message.currentTarget 3] .empty g' S' ss'
          returnData) fun evm =>
        Added (n + 1) message.currentTarget (requestWordsOf n message.caller message.data)
          (requestLog message.caller message.data) S ss evm ∧
        g ≤ evm.gas + 25000 * storageGasScale fork * (n + 4) := by
  induction k with
  | zero =>
    intro j hj _ S' g' ss' hw hacc hg hlogs
    have hn : j + 1 = n := hj
    subst hn
    have h := hc.last_then (returnData := returnData) hfork hstatic hsize hgas hw hacc
      (by rw [Nat.add_sub_cancel]; exact hg) hlogs
    rwa [show j + 1 - 2 = j - 1 by omega] at h
  | succ k ih =>
    intro j hj hj1 S' g' ss' hw hacc hg hlogs
    refine hc.word_then hj1 (by omega) hfork hstatic hgas hw hacc hg hlogs
      fun S'' g'' ss'' hw' hacc' hg' hlogs' => ?_
    have h := ih (j + 1) (by omega) (by omega) S'' g'' ss'' hw' hacc' hg' hlogs'
    rwa [Nat.add_sub_cancel] at h

/-- From byte 143, the code adds the request of the caller and the input.

It stores the words of the request at the tail of the queue, and logs the caller and the input. -/
theorem spec_add (hc : AddPathCode code n size) {S : TransactionState} {ss : Substate} {g : Nat}
    (hfork : .shapella ≤ fork) (hstatic : message.isStatic = false)
    (hacc : (S.getAccountOptional message.currentTarget).isSome = true)
    (hsize : message.data.size = size)
    -- The frame has 25,000 gas for each of the `n + 3` writes of the storage.
    --
    -- It has 25,000 more for the two reads and the log.
    --
    -- From Glamsterdam, each of these budgets is five times larger.
    (hgas : 25000 * storageGasScale fork * (n + 4) ≤ g) :
    -- From Glamsterdam, this one-counter frame is a model for the proof, not the meter of EIP-8037.
    Spec fork (At code message 143 [] .empty g S ss returnData) fun evm =>
      Added (n + 1) message.currentTarget (requestWordsOf n message.caller message.data)
        (requestLog message.caller message.data) S ss evm ∧
      -- The run spends at most that gas.
      g ≤ evm.gas + 25000 * storageGasScale fork * (n + 4) := by
  have h2 := hc.two_le
  -- The head needs the budget of four writes.
  have hhead : 100000 * storageGasScale fork ≤ g := by
    refine Nat.le_trans ?_ hgas
    rw [Nat.mul_comm 25000, Nat.mul_assoc, Nat.mul_comm 100000]
    exact Nat.mul_le_mul_left _ (by omega)
  refine hc.head_then hfork hstatic hacc hhead fun S' g' ss' hw hacc' hg hlogs => ?_
  have h := hc.words_then (returnData := returnData) (S := S) (ss := ss) hfork hstatic
    hsize hgas (n - 2) 1 (by omega) (Nat.le_refl 1)
  simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul] at h
  exact h S' g' ss' hw hacc' (by rw [Nat.mul_comm]; exact hg) hlogs

end AddPathCode

end EthLib.Execution.Blocks.RequestQueue
