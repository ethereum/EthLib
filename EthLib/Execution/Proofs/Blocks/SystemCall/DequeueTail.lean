module

public import EthLib.Execution.Proofs.Blocks.SystemCall.RequestQueue

/-!
# Proofs: the end of the system call of a request contract

The codes of EIP-7002 and EIP-7251 end their system call with the same 113 bytes, at two offsets.

Those bytes move the head of the queue, update the excess, reset the count and return the records.

The lemmas here run them once, for every code that holds them at any offset.
-/

@[expose] public section

namespace EthLib.Execution.Blocks.RequestQueue

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Blocks.SystemContract

/-- The 113 bytes of the end of the system call, the first byte highest, with 0 at each constant. -/
def DEQUEUE_TAIL_NUMBER : Nat :=
  0x5b91018092146100005790600255610000565b90505f6002555f6003555b5f54807fffffffffffff * 256 ^ 73 +
  0xffffffffffffffffffffffffffffffffffffffffffffffffffff141561000057505f5b6001546000 * 256 ^ 33 +
  0x828201116100005750505f610000565b01600090035b5f555f6001556000025ff3

/-- A code holds the end of the system call from the offset `o`. -/
structure DequeueTailCode (code : ByteArray) (o target size : Nat) : Prop where
  -- The bytes lie inside the code, and each jump destination fits in two bytes.
  size_le : o + 113 ≤ code.size
  end_lt : o + 113 < 2 ^ 16
  byte : ∀ i (h : o + i < code.size), i < 113 → i ≠ 7 → i ≠ 8 → i ≠ 15 → i ≠ 16 → i ≠ 69 →
    i ≠ 70 → i ≠ 79 → i ≠ 85 → i ≠ 86 → i ≠ 92 → i ≠ 93 → i ≠ 98 → i ≠ 109 →
    code[o + i] = NatCode.natByte DEQUEUE_TAIL_NUMBER 113 i
  -- The slot 2 twice, the slot 3, the inhibitor, and the slot 1 twice.
  --
  -- The bytes fix them; the step tactic reads them as words.
  push11 : pushData code (o + 11) 1 = BitVec.ofNat 256 2
  push22 : pushData code (o + 22) 1 = BitVec.ofNat 256 2
  push26 : pushData code (o + 26) 1 = BitVec.ofNat 256 3
  push33 : pushData code (o + 33) 32 = BitVec.ofNat 256 (2 ^ 256 - 1)
  push75 : pushData code (o + 75) 1 = BitVec.ofNat 256 1
  push105 : pushData code (o + 105) 1 = BitVec.ofNat 256 1
  -- The jumps land at `o` plus 18, 29, 74, 95 and 101.
  push6 : pushData code (o + 6) 2 = BitVec.ofNat 256 (o + 18)
  push14 : pushData code (o + 14) 2 = BitVec.ofNat 256 (o + 29)
  push68 : pushData code (o + 68) 2 = BitVec.ofNat 256 (o + 74)
  push84 : pushData code (o + 84) 2 = BitVec.ofNat 256 (o + 95)
  push91 : pushData code (o + 91) 2 = BitVec.ofNat 256 (o + 101)
  dest18 : isValidJumpDest (validJumpDestinations code) (o + 18) = true
  dest29 : isValidJumpDest (validJumpDestinations code) (o + 29) = true
  dest74 : isValidJumpDest (validJumpDestinations code) (o + 74) = true
  dest95 : isValidJumpDest (validJumpDestinations code) (o + 95) = true
  dest101 : isValidJumpDest (validJumpDestinations code) (o + 101) = true
  -- The target `target` of requests per block, twice, and the size `size` of a record.
  --
  -- Each is one byte.
  push78 : pushData code (o + 78) 1 = BitVec.ofNat 256 target
  push97 : pushData code (o + 97) 1 = BitVec.ofNat 256 target
  push108 : pushData code (o + 108) 1 = BitVec.ofNat 256 size
  target_lt : target < 256
  size_lt : size < 256

namespace DequeueTailCode

/-- The positions of the constants in the end of the system call. -/
def CONSTANTS : List Nat := [7, 8, 15, 16, 69, 70, 79, 85, 86, 92, 93, 98, 109]

/-- Whether the code stored in `n`, of `len` bytes, holds the end from `o`, except at constants. -/
def holdsNat (n len o : Nat) : Bool :=
  (List.range 113).all fun i =>
    CONSTANTS.contains i ||
      NatCode.natByte n len (o + i) == NatCode.natByte DEQUEUE_TAIL_NUMBER 113 i

/-- A code stored as a number holds the end, except at the constants, when the check passes. -/
theorem byte_ofNat {n len o : Nat} (hcheck : holdsNat n len o = true) :
    ∀ i (h : o + i < (NatCode.ofNat n len).size), i < 113 → i ≠ 7 → i ≠ 8 → i ≠ 15 →
      i ≠ 16 → i ≠ 69 → i ≠ 70 → i ≠ 79 → i ≠ 85 → i ≠ 86 → i ≠ 92 → i ≠ 93 → i ≠ 98 →
      i ≠ 109 → (NatCode.ofNat n len)[o + i] = NatCode.natByte DEQUEUE_TAIL_NUMBER 113 i := by
  intro i h hi h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  rw [NatCode.getElem_ofNat]
  simp only [holdsNat, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    List.contains_iff_mem] at hcheck
  rcases hcheck i hi with hm | he
  · simp [CONSTANTS] at hm
    omega
  · exact he

variable {code : ByteArray} {o target size : Nat} (hc : DequeueTailCode code o target size)
  {fork : Fork} {message : Message fork} {returnData : ByteArray}

include hc

/-- Each byte of the end lies inside the code. -/
theorem lt_size {i : Nat} (hi : i < 113) : o + i < code.size := by
  have := hc.size_le
  omega

/-- A jump destination of the end, as a word, gives back its position. -/
theorem toNat_dest {k : Nat} (hk : k ≤ 113) : (BitVec.ofNat 256 (o + k)).toNat = o + k := by
  have := hc.end_lt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- JUMPI to a destination of the end, on a condition that is not 0, lands there for 10 gas. -/
theorem jumpi_to {pc k : Nat} {condition : U256} {rest : List U256} {memory : ByteArray}
    {gas : Nat} {state : TransactionState} {substate : Substate} (hk : k ≤ 113)
    (hdest : isValidJumpDest (validJumpDestinations code) (o + k) = true)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x57) (hcond : condition ≠ 0) (hgas : 10 ≤ gas) :
    Hoare fork (At code message pc (BitVec.ofNat 256 (o + k) :: condition :: rest) memory gas
        state substate returnData)
      (At code message (o + k) rest memory (gas - 10) state substate returnData) := by
  have h := jumpi_taken (fork := fork) (message := message) (memory := memory) (state := state)
    (substate := substate) (returnData := returnData) (rest := rest) hlt hbyte hgas hcond
    (by rw [hc.toNat_dest hk]; exact hdest)
  rw [hc.toNat_dest hk] at h
  exact h

/-- JUMP to a destination of the end lands there for 8 gas. -/
theorem jump_to {pc k : Nat} {rest : List U256} {memory : ByteArray} {gas : Nat}
    {state : TransactionState} {substate : Substate} (hk : k ≤ 113)
    (hdest : isValidJumpDest (validJumpDestinations code) (o + k) = true)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x56) (hgas : 8 ≤ gas) :
    Hoare fork (At code message pc (BitVec.ofNat 256 (o + k) :: rest) memory gas state substate
        returnData)
      (At code message (o + k) rest memory (gas - 8) state substate returnData) := by
  have h := jump (fork := fork) (message := message) (memory := memory) (state := state)
    (substate := substate) (returnData := returnData) (rest := rest) hlt hbyte hgas
    (by rw [hc.toNat_dest hk]; exact hdest)
  rw [hc.toNat_dest hk] at h
  exact h

set_option hygiene false in
/-- Runs one step of the end, reading its bytes from the facts of `hc` and `hl`. -/
local macro "tail_step" : tactic => `(tactic| evm_step [hc.byte, hl, hc.push11, hc.push22,
  hc.push26, hc.push33, hc.push75, hc.push105, hc.push6, hc.push14, hc.push68, hc.push84,
  hc.push91, hc.push78, hc.push97, hc.push108, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
  DEQUEUE_TAIL_NUMBER, Nat.add_assoc])

set_option hygiene false in
/-- Proves a fact about a byte of the end, from the facts of `hc` and `hl`. -/
local macro "tail_code" : tactic => `(tactic| evm_code [hc.byte, hl, ne_eq, Nat.reduceEqDiff,
  not_false_eq_true, DEQUEUE_TAIL_NUMBER, Nat.add_assoc])

/-- From `o + 101`, the code writes the excess `v`, resets the count, and returns the records. -/
theorem spec_end {S : TransactionState} {ss : Substate} {M : ByteArray} {g : Nat}
    {v x : U256} (hfork : .shapella ≤ fork)
    (hstatic : message.isStatic = false)
    (hacc : (S.getAccountOptional message.currentTarget).isSome = true)
    -- Memory holds the records, `size` bytes for each of the `x` requests taken.
    (hM : (mul (BitVec.ofNat 256 size) x).toNat ≤ M.size)
    (hg : 50000 * storageGasScale fork ≤ g) :
    Spec fork (At code message (o + 101) [v, x] M g S ss returnData)
      (Returned message.currentTarget M (mul (BitVec.ofNat 256 size) x).toNat
        (setSlot (setSlot (storageOf S message.currentTarget) 0 v) 1 0) S) := by
  have hl : ∀ i, i < 113 → o + i < code.size := fun _ h => hc.lt_size h
  have hscale := one_le_storageGasScale fork
  tail_step
  tail_step
  refine sstore_then (Nat.le_trans (by decide) hfork) (by tail_code) (by tail_code) hstatic hacc
    (by omega) fun S₁ hw₁ hacc₁ g₁ ss₁ hg₁ _ => ?_
  tail_step
  tail_step
  refine sstore_then (Nat.le_trans (by decide) hfork) (by tail_code) (by tail_code) hstatic hacc₁
    (by omega) fun S₂ hw₂ _ g₂ ss₂ hg₂ _ => ?_
  tail_step
  tail_step
  tail_step
  have hle : extendMemory M.size [((0 : U256), mul (BitVec.ofNat 256 size) x)] = ⟨0, 0⟩ :=
    extendMemory_of_le (by simpa using hM)
  refine Spec.consequence («return» (by tail_code) (by tail_code)
    (by rw [hle]; exact Nat.zero_le _)) (fun _ h => h) ?_
  rintro evm ⟨-, herr, hout, -, hst, -⟩
  refine ⟨by simpa using herr, ?_, ?_⟩
  · rw [hout, hle]
    dsimp only
    rw [memoryExtend_zero]
    rfl
  · rw [hst]
    have hw := WritesStorage.trans hw₁ hw₂
    rw [show storageOf S₁ message.currentTarget = _ from funext hw₁.1] at hw
    exact hw

/-- From `o + 74`, the code computes the new excess from the previous excess `p` and the count.

The previous excess plus the count is below `2^256`. -/
theorem spec_count {S : TransactionState} {ss : Substate} {M : ByteArray} {g p : Nat}
    {x : U256} (hfork : .shapella ≤ fork)
    (hstatic : message.isStatic = false)
    (hacc : (S.getAccountOptional message.currentTarget).isSome = true)
    (hp : p + (storageOf S message.currentTarget 1#256).toNat < 2 ^ 256)
    (hM : (mul (BitVec.ofNat 256 size) x).toNat ≤ M.size)
    (hg : 60000 * storageGasScale fork ≤ g) :
    Spec fork (At code message (o + 74) [BitVec.ofNat 256 p, x] M g S ss returnData)
      (Returned message.currentTarget M (mul (BitVec.ofNat 256 size) x).toNat
        (setSlot (setSlot (storageOf S message.currentTarget) 0
          (BitVec.ofNat 256 (if p + (storageOf S message.currentTarget 1#256).toNat > target then
            p + (storageOf S message.currentTarget 1#256).toNat - target else 0))) 1 0) S) := by
  have hl : ∀ i, i < 113 → o + i < code.size := fun _ h => hc.lt_size h
  have hscale := one_le_storageGasScale fork
  have ht := hc.target_lt
  generalize hn : (storageOf S message.currentTarget 1#256).toNat = n at hp
  have hs : add (storageOf S message.currentTarget 1#256) (BitVec.ofNat 256 p) =
      BitVec.ofNat 256 (p + n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [add, BitVec.toNat_add, BitVec.toNat_ofNat, hn]
    have hp' : p < 2 ^ 256 := Nat.lt_of_le_of_lt (Nat.le_add_right p n) hp
    rw [Nat.mod_eq_of_lt hp', Nat.add_comm, Nat.mod_eq_of_lt hp]
  tail_step
  tail_step
  refine sload_then (Nat.le_trans (by decide) hfork) (by tail_code) (by tail_code) (by omega)
    fun g₁ ss₁ hg₁ _ => ?_
  have hacc₁ : ((S.recordStorageRead message.currentTarget (U256.toBeBytes 1#256)
      ).getAccountOptional message.currentTarget).isSome = true := hacc
  tail_step
  tail_step
  tail_step
  tail_step
  rw [hs]
  have hsub : target ≤ p + n → sub (BitVec.ofNat 256 (p + n)) (BitVec.ofNat 256 target) =
      BitVec.ofNat 256 (p + n - target) := by
    intro h2
    apply BitVec.eq_of_toNat_eq
    simp only [sub, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp,
      Nat.mod_eq_of_lt (by omega : target < 2 ^ 256)]
    omega
  have post : ∀ v, ∀ evm : Evm fork Nat, Returned message.currentTarget M
      (mul (BitVec.ofNat 256 size) x).toNat
      (setSlot (setSlot (storageOf S message.currentTarget) 0 v) 1 0)
      (S.recordStorageRead message.currentTarget (U256.toBeBytes 1#256)) evm →
      Returned message.currentTarget M (mul (BitVec.ofNat 256 size) x).toNat
        (setSlot (setSlot (storageOf S message.currentTarget) 0 v) 1 0) S evm :=
    fun _ _ ⟨h1, h2, h3⟩ =>
      ⟨h1, h2, WritesStorage.trans (WritesStorage.recordStorageRead _ _ _ _) h3⟩
  by_cases hgt : p + n > target
  · have hz : greaterThan (BitVec.ofNat 256 (p + n)) (BitVec.ofNat 256 target) ≠ 0 := by
      simp [greaterThan, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt (by omega : target < 2 ^ 256),
        hgt]
    tail_step
    tail_step
    refine Triple.seq (hc.jumpi_to (k := 95) (by decide) hc.dest95 (by tail_code)
      (by tail_code) hz (by omega)) ?_
    tail_step
    tail_step
    rw [hs]
    tail_step
    tail_step
    tail_step
    rw [hsub (by omega)]
    simp only [hgt, ite_true]
    exact Spec.consequence (hc.spec_end hfork hstatic hacc₁ hM (by omega)) (fun _ h => h)
      (post _)
  · have hz : greaterThan (BitVec.ofNat 256 (p + n)) (BitVec.ofNat 256 target) = 0 := by
      simp [greaterThan, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt (by omega : target < 2 ^ 256),
        hgt]
    tail_step
    tail_step
    tail_step
    tail_step
    tail_step
    tail_step
    tail_step
    refine Triple.seq (hc.jump_to (k := 101) (by decide) hc.dest101 (by tail_code)
      (by tail_code) (by omega)) ?_
    simp only [hgt, ite_false]
    exact Spec.consequence (hc.spec_end hfork hstatic hacc₁ hM (by omega)) (fun _ h => h)
      (post _)

/-- From `o + 29`, the code updates the excess for the target per block, and resets the count.

It then returns the records, `size` bytes for each request taken. -/
theorem spec_excess {S : TransactionState} {ss : Substate} {M : ByteArray} {g : Nat}
    {x : U256} (hfork : .shapella ≤ fork)
    (hstatic : message.isStatic = false)
    (hacc : (S.getAccountOptional message.currentTarget).isSome = true)
    (hb : previousExcess (storageOf S message.currentTarget 0) +
      (storageOf S message.currentTarget 1#256).toNat < 2 ^ 256)
    (hM : (mul (BitVec.ofNat 256 size) x).toNat ≤ M.size)
    (hg : 70000 * storageGasScale fork ≤ g) :
    Spec fork (At code message (o + 29) [x] M g S ss returnData)
      (Returned message.currentTarget M (mul (BitVec.ofNat 256 size) x).toNat
        (setSlot (setSlot (storageOf S message.currentTarget) 0
          (BitVec.ofNat 256 (newExcess target (storageOf S message.currentTarget 0)
            (storageOf S message.currentTarget 1)))) 1 0) S) := by
  have hl : ∀ i, i < 113 → o + i < code.size := fun _ h => hc.lt_size h
  have hscale := one_le_storageGasScale fork
  tail_step
  tail_step
  refine sload_then (Nat.le_trans (by decide) hfork) (by tail_code) (by tail_code) (by omega)
    fun g₁ ss₁ hg₁ _ => ?_
  have hacc₁ : ((S.recordStorageRead message.currentTarget (U256.toBeBytes 0)).getAccountOptional
      message.currentTarget).isSome = true := hacc
  have post : ∀ evm : Evm fork Nat, Returned message.currentTarget M
      (mul (BitVec.ofNat 256 size) x).toNat
      (setSlot (setSlot (storageOf S message.currentTarget) 0
        (BitVec.ofNat 256 (newExcess target (storageOf S message.currentTarget 0)
          (storageOf S message.currentTarget 1)))) 1 0)
      (S.recordStorageRead message.currentTarget (U256.toBeBytes 0)) evm →
      Returned message.currentTarget M (mul (BitVec.ofNat 256 size) x).toNat
        (setSlot (setSlot (storageOf S message.currentTarget) 0
          (BitVec.ofNat 256 (newExcess target (storageOf S message.currentTarget 0)
            (storageOf S message.currentTarget 1)))) 1 0) S evm :=
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, h2, WritesStorage.trans (WritesStorage.recordStorageRead _ _ _ _) h3⟩
  have hw : BitVec.ofNat 256 (2 ^ 256 - 1) = EXCESS_INHIBITOR := rfl
  by_cases hinh : storageOf S message.currentTarget 0 = EXCESS_INHIBITOR
  · have hz : isZero (equal (BitVec.ofNat 256 (2 ^ 256 - 1))
        (storageOf S message.currentTarget 0)) = 0 := by
      rw [hinh, ← hw]
      decide
    simp only [Nat.reducePow, Nat.reduceSub] at hz
    tail_step
    tail_step
    tail_step
    tail_step
    tail_step
    tail_step
    tail_step
    tail_step
    have hp : previousExcess (storageOf S message.currentTarget 0) = 0 := by
      unfold previousExcess
      rw [ite_eq_left hinh]
    rw [hp] at hb
    refine Spec.consequence (hc.spec_count (p := 0) hfork hstatic hacc₁ hb hM (by omega))
      (fun _ h => h) fun evm h => post evm ?_
    unfold newExcess
    rw [hp]
    exact h
  · have hz : isZero (equal (BitVec.ofNat 256 (2 ^ 256 - 1))
        (storageOf S message.currentTarget 0)) ≠ 0 := by
      have hne : BitVec.ofNat 256 (2 ^ 256 - 1) ≠ storageOf S message.currentTarget 0 :=
        fun e => hinh (e.symm.trans hw)
      rw [equal, ite_eq_right hne, isZero, ite_eq_left rfl]
      decide
    simp only [Nat.reducePow, Nat.reduceSub] at hz
    tail_step
    tail_step
    tail_step
    tail_step
    tail_step
    refine Triple.seq (hc.jumpi_to (k := 74) (by decide) hc.dest74 (by tail_code)
      (by tail_code) hz (by omega)) ?_
    have hp : previousExcess (storageOf S message.currentTarget 0) =
        (storageOf S message.currentTarget 0).toNat := by
      unfold previousExcess
      rw [ite_eq_right hinh]
    rw [hp] at hb
    refine Spec.reshape (s' := [BitVec.ofNat 256 (storageOf S message.currentTarget 0).toNat, x])
      (by simp) rfl rfl ?_
    refine Spec.consequence (hc.spec_count hfork hstatic hacc₁ hb hM (by omega))
      (fun _ h => h) fun evm h => post evm ?_
    unfold newExcess
    rw [hp]
    exact h

/-- From `o`, the code moves the head of the queue, or empties it, then updates the excess.

It returns the records of the requests it took, which memory holds. -/
theorem spec_head {S : TransactionState} {ss : Substate} {M : ByteArray} {g max : Nat}
    {r : U256 → U256} (hfork : .shapella ≤ fork)
    (hstatic : message.isStatic = false)
    (hacc : (S.getAccountOptional message.currentTarget).isSome = true)
    (hr : storageOf S message.currentTarget = r) (hb : Bounded r)
    -- The records of the most requests that a block takes fit in a word.
    (hmax : size * max < 2 ^ 256)
    (hMs : size * numDequeued max r ≤ M.size) (hg : 120000 * storageGasScale fork ≤ g) :
    Spec fork (At code message o [BitVec.ofNat 256 (numDequeued max r),
        BitVec.ofNat 256 (numDequeued max r), r 2, r 3] M g S ss returnData)
      (Returned message.currentTarget M (size * numDequeued max r) (afterDequeue max target r)
        S) := by
  have hl : ∀ i, i < 113 → o + i < code.size := fun _ h => hc.lt_size h
  have hscale := one_le_storageGasScale fork
  obtain ⟨hht, hex⟩ := hb
  have hc2 : numDequeued max r ≤ max := Nat.min_le_right _ _
  have hle : (r 2).toNat + numDequeued max r ≤ (r 3).toNat := by
    unfold numDequeued
    have h : Nat.min ((r 3).toNat - (r 2).toNat) max ≤ (r 3).toNat - (r 2).toNat :=
      Nat.min_le_left _ _
    omega
  have ht := (r 3).isLt
  have hsz := hc.size_lt
  generalize hc' : numDequeued max r = c at hc2 hle hMs ⊢
  have hcm : size * c < 2 ^ 256 := Nat.lt_of_le_of_lt (Nat.mul_le_mul_left size hc2) hmax
  have hnh : add (r 2) (BitVec.ofNat 256 c) = BitVec.ofNat 256 ((r 2).toNat + c) := by
    apply BitVec.eq_of_toNat_eq
    simp only [add, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : c < 2 ^ 256), Nat.mod_eq_of_lt (by omega)]
  have hmul : (mul (BitVec.ofNat 256 size) (BitVec.ofNat 256 c)).toNat = size * c := by
    simp only [mul, BitVec.toNat_mul, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : c < 2 ^ 256), Nat.mod_eq_of_lt (by omega : size < 2 ^ 256)]
    exact Nat.mod_eq_of_lt hcm
  have hM : (mul (BitVec.ofNat 256 size) (BitVec.ofNat 256 c)).toNat ≤ M.size := by
    rw [hmul]; exact hMs
  have hr0 : ∀ F : U256 → U256, F 0 = r 0 → F 1#256 = r 1 →
      previousExcess (F 0) + (F 1#256).toNat < 2 ^ 256 := fun F h0 h1 => by
    rw [h0, h1]; exact hex
  change Spec fork (At code message (o + 0) _ _ _ _ _ _) _
  tail_step
  tail_step
  tail_step
  rw [hnh]
  tail_step
  tail_step
  tail_step
  tail_step
  have heqv : r 3 = BitVec.ofNat 256 ((r 2).toNat + c) ↔ (r 2).toNat + c = (r 3).toNat := by
    constructor
    · intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      omega
    · intro e
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
  by_cases hnt : (r 2).toNat + c = (r 3).toNat
  · have hz : equal (r 3) (BitVec.ofNat 256 ((r 2).toNat + c)) ≠ 0 := by
      rw [equal, ite_eq_left (heqv.mpr hnt)]
      decide
    refine Triple.seq (hc.jumpi_to (k := 18) (by decide) hc.dest18 (by tail_code)
      (by tail_code) hz (by omega)) ?_
    tail_step
    tail_step
    tail_step
    tail_step
    tail_step
    refine sstore_then (Nat.le_trans (by decide) hfork) (by tail_code) (by tail_code) hstatic hacc
      (by omega) fun S₁ hw₁ hacc₁ g₁ ss₁ hg₁ _ => ?_
    tail_step
    tail_step
    refine sstore_then (Nat.le_trans (by decide) hfork) (by tail_code) (by tail_code) hstatic
      hacc₁ (by omega) fun S₂ hw₂ hacc₂ g₂ ss₂ hg₂ _ => ?_
    have eF : storageOf S₂ message.currentTarget = setSlot (setSlot r 2 0) 3 0 := by
      rw [funext hw₂.1, funext hw₁.1, hr]
      rfl
    refine Spec.consequence (hc.spec_excess hfork hstatic hacc₂
      (hr0 _ (by rw [eF]; simp [setSlot]) (by rw [eF]; simp [setSlot])) hM (by omega))
      (fun _ h => h) fun evm h => ?_
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, by rw [h2, hmul], ?_⟩
    have hw := WritesStorage.trans (WritesStorage.trans hw₁ hw₂) h3
    rw [eF, deq_store max target r (setSlot (setSlot r 2 0) 3 0)
      (by rw [hc', ite_eq_left hnt])] at hw
    exact hw
  · have hz : equal (r 3) (BitVec.ofNat 256 ((r 2).toNat + c)) = 0 := by
      simp only [equal]
      rw [ite_eq_right_iff]
      exact fun e => absurd (heqv.mp e) hnt
    tail_step
    tail_step
    tail_step
    refine sstore_then (Nat.le_trans (by decide) hfork) (by tail_code) (by tail_code) hstatic hacc
      (by omega) fun S₁ hw₁ hacc₁ g₁ ss₁ hg₁ _ => ?_
    tail_step
    refine Triple.seq (hc.jump_to (k := 29) (by decide) hc.dest29 (by tail_code)
      (by tail_code) (by omega)) ?_
    have eF : storageOf S₁ message.currentTarget =
        setSlot r 2 (BitVec.ofNat 256 ((r 2).toNat + c)) := by
      rw [funext hw₁.1, hr]
      rfl
    refine Spec.consequence (hc.spec_excess hfork hstatic hacc₁
      (hr0 _ (by rw [eF]; simp [setSlot]) (by rw [eF]; simp [setSlot])) hM (by omega))
      (fun _ h => h) fun evm h => ?_
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, by rw [h2, hmul], ?_⟩
    have hw := WritesStorage.trans hw₁ h3
    rw [eF, deq_store max target r (setSlot r 2 (BitVec.ofNat 256 ((r 2).toNat + c)))
      (by rw [hc', ite_eq_right hnt])] at hw
    exact hw

end DequeueTailCode

end EthLib.Execution.Blocks.RequestQueue
