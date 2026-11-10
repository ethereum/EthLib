module

public import EthLib.Execution.Proofs.Blocks.SystemCall.Contract
public import EthLib.Execution.Proofs.Fees.BlobBaseFee
public import EthLib.Execution.Proofs.Evm.Instructions.Arithmetic
public import EthLib.Execution.Proofs.Evm.Instructions.Bitwise
public import EthLib.Execution.Proofs.Evm.Logic.Log

/-!
# Proofs: what the request contracts share

The withdrawal request contract of [EIP-7002][eip-7002] keeps a queue of requests in its storage.

The consolidation request contract of [EIP-7251][eip-7251] keeps one as well.

Both keep the same four counters in the first four slots of their storage.

Slot 0 holds the excess of requests, slot 1 the number of requests added in the block.

Slots 2 and 3 hold the indices of the head and the tail of the queue.

The requests follow from slot 4, each in a fixed number of slots.

A call from any other address with no input and no value gets the fee to add a request.

A call with a request as its input and at least the fee adds the request at the tail.

The fee is an exponential of the excess, computed by the loop of `fake_exponential`.

Until the first system call, the excess holds the inhibitor, and no request can be added.

A call from the system address takes at most a fixed number of requests from the head.

It then updates the excess with the number of requests of the block, and resets that number.

The EIPs compute on integers, and the code computes on words of 256 bits.

The two agree while no value reaches `2^256`.

Here, as in the code, each slot and each value written to it is a word, modulo `2^256`.

The bounds that a theorem needs on the counters and on the fee come as hypotheses.

[eip-7002]: https://eips.ethereum.org/EIPS/eip-7002#withdrawal-request-contract
[eip-7251]: https://eips.ethereum.org/EIPS/eip-7251#consolidation-request-contract
-/

@[expose] public section

namespace EthLib.Execution.Blocks.RequestQueue

open EthLib.Base (U256)
open EthLib.Execution.Fees.BlobBaseFee (accum partialSum fakeExponential partialSum_le_of_le)

/-! ## The fee -/

/-- The excess that blocks any request before the first system call, `2^256 - 1`. -/
def EXCESS_INHIBITOR : U256 := BitVec.allOnes 256

/-- The fee to add a request at the excess `excess`, or none while the inhibitor holds.

It approximates `factor * e^(excess / fraction)` by the integer loop of `fake_exponential`. -/
def getFee (factor fraction : Nat) (excess : U256) : Option Nat :=
  if excess = EXCESS_INHIBITOR then none else some (fakeExponential factor excess.toNat fraction)

/-- The loop of the fee stops within `m` steps, and computes on words with no overflow.

Its accumulator is 0 at step `m`, and the sum of the accumulators before it is below `2^256`.

Each product of an accumulator before step `m` and the excess is below `2^256`.

So is `fraction * (m + 1)`, which bounds every divisor of the loop.

The loop of the code fixes the factor at 1. -/
def FeeFits (factor fraction excess m : Nat) : Prop :=
  accum factor excess fraction m = 0 ∧ partialSum factor excess fraction m < 2 ^ 256 ∧
    fraction * (m + 1) < 2 ^ 256 ∧ ∀ k < m, accum factor excess fraction k * excess < 2 ^ 256

/-! ## The storage -/

/-- The storage `read` with the word `value` at the slot `key`. -/
def setSlot (read : U256 → U256) (key value : U256) (slot : U256) : U256 :=
  if slot = key then value else read slot

/-- The excess that the next fee starts from: the excess word, or 0 while the inhibitor holds. -/
def previousExcess (excess : U256) : Nat :=
  if excess = EXCESS_INHIBITOR then 0 else excess.toNat

/-- The excess after a block with `count` requests, for a target of `target` per block.

It is the previous excess plus the count, less the target, or 0 when that is not positive. -/
def newExcess (target : Nat) (excess count : U256) : Nat :=
  if previousExcess excess + count.toNat > target then
    previousExcess excess + count.toNat - target
  else 0

/-- The number of requests that a block takes from the queue: at most `max`.

It is 0 when the head is past the tail, where the code instead takes `max`. -/
def numDequeued (max : Nat) (read : U256 → U256) : Nat :=
  Nat.min ((read 3).toNat - (read 2).toNat) max

/-- The storage after a request of the words `words` is added, from the storage `read`.

The count of the block grows by one.

The words go to the slots of the request at the tail, from slot 4, `size` slots per request.

The tail then grows by one.

The writes come in this order, as in the EIP. -/
def afterAdd (size : Nat) (words : List U256) (read : U256 → U256) : U256 → U256 :=
  let start := 4 + read 3 * BitVec.ofNat 256 size
  let counted := setSlot read 1 (read 1 + 1)
  let stored := (words.zipIdx.foldl fun r (word, j) => setSlot r (start + BitVec.ofNat 256 j) word)
    counted
  setSlot stored 3 (read 3 + 1)

/-- The storage after the system call of a block, from the storage `read`.

The call takes at most `max` requests from the head, with a target of `target` per block.

When it empties the queue, the head and the tail go back to 0.

Otherwise the head moves past the requests it took.

The excess is the new excess of the block, and the count of the block is 0.

Every other slot keeps its word. -/
def afterDequeue (max target : Nat) (read : U256 → U256) (slot : U256) : U256 :=
  let head := (read 2).toNat
  let tail := (read 3).toNat
  let next := head + numDequeued max read
  if slot = 0 then BitVec.ofNat 256 (newExcess target (read 0) (read 1))
  else if slot = 1 then 0
  else if slot = 2 then (if next = tail then 0 else BitVec.ofNat 256 next)
  else if slot = 3 then (if next = tail then 0 else read 3)
  else read slot

/-- The writes of the system call give the storage after the requests are taken.

The head and the tail go back to 0 when the queue empties, and the head moves on otherwise.

Then the excess is updated and the count reset. -/
theorem deq_store (max target : Nat) (r : U256 → U256) (F : U256 → U256)
    (hF : F = if (r 2).toNat + numDequeued max r = (r 3).toNat then setSlot (setSlot r 2 0) 3 0
      else setSlot r 2 (BitVec.ofNat 256 ((r 2).toNat + numDequeued max r))) :
    setSlot (setSlot F 0 (BitVec.ofNat 256 (newExcess target (F 0) (F 1)))) 1 0 =
      afterDequeue max target r := by
  funext slot
  subst hF
  by_cases h : (r 2).toNat + numDequeued max r = (r 3).toNat
  · simp only [h, ite_true, setSlot, afterDequeue]
    by_cases h1 : slot = 1
    · simp [h1]
    · by_cases h0 : slot = 0
      · simp [h0]
      · by_cases h2 : slot = 2
        · simp [h2]
        · by_cases h3 : slot = 3
          · simp [h3]
          · simp_all
  · simp only [h, ite_false, setSlot, afterDequeue]
    by_cases h1 : slot = 1
    · simp [h1]
    · by_cases h0 : slot = 0
      · simp [h0]
      · by_cases h2 : slot = 2
        · simp [h2]
        · by_cases h3 : slot = 3
          · simp [h3]
          · simp_all

/-- The records of the first `k` requests from the head, in the order of the queue.

The record of a request is `record` of the storage `read` and its index in the queue. -/
def taken (record : (U256 → U256) → U256 → ByteArray) (read : U256 → U256) (k : Nat) :
    ByteArray :=
  (List.range k).foldl (fun acc i => acc ++ record read (read 2 + BitVec.ofNat 256 i)) .empty

/-- The requests that the system call of a block returns, from the storage `read`.

They are the records of the at most `max` requests that the block takes from the head. -/
def dequeued (max : Nat) (record : (U256 → U256) → U256 → ByteArray) (read : U256 → U256) :
    ByteArray :=
  taken record read (numDequeued max read)

/-- The counters meet the bounds under which the code computes as the EIP.

The head of the queue is not past its tail.

The previous excess plus the count of the block is below `2^256`. -/
def Bounded (read : U256 → U256) : Prop :=
  (read 2).toNat ≤ (read 3).toNat ∧ previousExcess (read 0) + (read 1).toNat < 2 ^ 256

/-- The records of the first `k + 1` requests from the head.

They are the records of the first `k`, then the record of request `k`. -/
theorem taken_succ (record : (U256 → U256) → U256 → ByteArray) (read : U256 → U256) (k : Nat) :
    taken record read (k + 1) =
      taken record read k ++ record read (read 2 + BitVec.ofNat 256 k) := by
  rw [taken, taken, List.range_succ, List.foldl_append]
  rfl

/-- The records of `k` requests have `size * k` bytes, when each record has `size` bytes. -/
theorem size_taken {record : (U256 → U256) → U256 → ByteArray} {size : Nat}
    (h : ∀ read index, (record read index).size = size) (read : U256 → U256) (k : Nat) :
    (taken record read k).size = size * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [taken_succ, ByteArray.size_append, ih, h, Nat.mul_succ]

/-! ## The loop of the fee in the code -/

section FeeLoop

open EthLib.Execution.Evm EthLib.Execution.Evm.Logic
open EthLib.Execution.Fees.BlobBaseFee (fakeExponential_eq_partialSum)

/-- The 44 bytes from byte 69 of the code of both contracts, the first byte highest.

They start the accumulator, run the loop of the fee, and leave the fee on the stack. -/
def FEE_LOOP_NUMBER : Nat :=
  0x600182026001905f5b5f82111560685781019083028483029004916001019190604d565b9093900492505050

/-- A code runs the loop of the fee from byte 69 to byte 112, as both contracts do.

Its bytes there are those of the loop, and bytes 77 and 104 are valid jump destinations. -/
structure FeeLoopCode (code : ByteArray) : Prop where
  size : 113 ≤ code.size
  byte : ∀ i (h : i < code.size), 68 < i → i < 113 →
    code[i] = NatCode.natByte FEE_LOOP_NUMBER 44 (i - 69)
  push : ∀ pc k, 68 < pc → pc + k < 113 →
    pushData code pc k =
      BitVec.ofNat 256 (FEE_LOOP_NUMBER >>> (8 * (44 - 1 - (pc - 69 + k))) % 256 ^ k)
  dest77 : isValidJumpDest (validJumpDestinations code) 77 = true
  dest104 : isValidJumpDest (validJumpDestinations code) 104 = true

/-- A code stored as a number runs the loop of the fee when its bytes 69 to 112 are those of it.

Bytes 77 and 104 must also be valid jump destinations. -/
theorem FeeLoopCode.of_ofNat {n size : Nat} (hsize : 113 ≤ size)
    (hwin : n >>> (8 * (size - 113)) % 256 ^ 44 = FEE_LOOP_NUMBER)
    (h77 : isValidJumpDest (validJumpDestinations (NatCode.ofNat n size)) 77 = true)
    (h104 : isValidJumpDest (validJumpDestinations (NatCode.ofNat n size)) 104 = true) :
    FeeLoopCode (NatCode.ofNat n size) := by
  have hpow : (256 : Nat) ^ 44 = 2 ^ (8 * 44) := (Nat.pow_mul 2 8 44).symm
  refine ⟨by rw [NatCode.size_ofNat]; exact hsize, fun i h h1 h2 => ?_, fun pc k h1 h2 => ?_,
    h77, h104⟩
  · have hi : i < size := by omega
    have hi' : i - 69 < 44 := by omega
    rw [NatCode.getElem_ofNat, NatCode.natByte, NatCode.natByte]
    simp only [hi, hi', ↓reduceIte]
    rw [← hwin, hpow,
      show 8 * (size - 1 - i) = 8 * (size - 113) + 8 * (44 - 1 - (i - 69)) by omega,
      Nat.shiftRight_add]
    apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_ofNat']
    apply NatCode.shiftRight_mod_two_pow
    omega
  · rw [NatCode.pushData_ofNat n size pc k (by omega), ← hwin, hpow,
      show 8 * (size - 1 - (pc + k)) = 8 * (size - 113) + 8 * (44 - 1 - (pc - 69 + k)) by omega,
      Nat.shiftRight_add, show (256 : Nat) ^ k = 2 ^ (8 * k) by rw [Nat.pow_mul]]
    congr 1
    apply NatCode.shiftRight_mod_two_pow
    omega

variable {fork : EthLib.Base.Fork} {code : ByteArray} {message : Message fork}
  {memory : ByteArray} {state : State.TransactionState} {substate : Substate}
  {returnData : ByteArray}

/-- At the head of the loop at byte 77, an accumulator of 0 leaves the loop.

The code divides the sum by the fraction, and reaches byte 113 with the fee, for 49 gas. -/
theorem feeLoop_exit (hfork : .shapella ≤ fork) (hc : FeeLoopCode code) {x : U256}
    {d j g : Nat} (hacc : accum 1 x.toNat d j = 0) (hps : partialSum 1 x.toNat d j < 2 ^ 256)
    (hd : d < 2 ^ 256) (hg : 49 ≤ g) :
    Hoare fork (At code message 77 [BitVec.ofNat 256 (partialSum 1 x.toNat d j),
        BitVec.ofNat 256 (accum 1 x.toNat d j), BitVec.ofNat 256 (j + 1), x, BitVec.ofNat 256 d]
        memory g state substate returnData)
      (At code message 113 [BitVec.ofNat 256 (fakeExponential 1 x.toNat d)] memory (g - 49)
        state substate returnData) := by
  have hb := hc.byte
  have hp := hc.push
  have hl : ∀ i, i < 113 → i < code.size := fun i h => by have := hc.size; omega
  rw [hacc]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  refine Triple.seq (jumpi_taken (hl 84 (by decide)) (by evm_code [hb, hp, hl, FEE_LOOP_NUMBER])
    (by omega) (by decide) hc.dest104) ?_
  simp only [BitVec.reduceToNat]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  refine reshape ?_ rfl rfl
  rw [fakeExponential_eq_partialSum hacc, div_ofNat hps hd]

/-- At the head of the loop at byte 77, a run of the loop adds the accumulator to the sum.

It then computes the next accumulator, and comes back to the head, for 87 gas.

The products and the sum stay below `2^256`. -/
theorem feeLoop_body (hfork : .shapella ≤ fork) (hc : FeeLoopCode code) {x : U256}
    {d j g : Nat} (hacc : accum 1 x.toNat d j ≠ 0)
    (hmul : accum 1 x.toNat d j * x.toNat < 2 ^ 256)
    (hps : partialSum 1 x.toNat d (j + 1) < 2 ^ 256) (hd : d * (j + 1) < 2 ^ 256)
    (hg : 87 ≤ g) :
    Hoare fork (At code message 77 [BitVec.ofNat 256 (partialSum 1 x.toNat d j),
        BitVec.ofNat 256 (accum 1 x.toNat d j), BitVec.ofNat 256 (j + 1), x, BitVec.ofNat 256 d]
        memory g state substate returnData)
      (At code message 77 [BitVec.ofNat 256 (partialSum 1 x.toNat d (j + 1)),
        BitVec.ofNat 256 (accum 1 x.toNat d (j + 1)), BitVec.ofNat 256 (j + 1 + 1), x,
        BitVec.ofNat 256 d] memory (g - 87) state substate returnData) := by
  have hb := hc.byte
  have hp := hc.push
  have hl : ∀ i, i < 113 → i < code.size := fun i h => by have := hc.size; omega
  have ha : accum 1 x.toNat d j < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hps
  have hz : isZero (greaterThan (BitVec.ofNat 256 (accum 1 x.toNat d j)) 0) = 0 := by
    simp [isZero, greaterThan, Nat.mod_eq_of_lt ha, Nat.pos_of_ne_zero hacc]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  refine Triple.seq (jump (hl 103 (by decide)) (by evm_code [hb, hp, hl, FEE_LOOP_NUMBER])
    (by omega) hc.dest77) ?_
  simp only [BitVec.reduceToNat]
  have e1 : mul x (BitVec.ofNat 256 (accum 1 x.toNat d j)) =
      BitVec.ofNat 256 (accum 1 x.toNat d j * x.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [mul, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mul_comm]
  have e2 : mul (BitVec.ofNat 256 (j + 1)) (BitVec.ofNat 256 d) =
      BitVec.ofNat 256 (d * (j + 1)) := by
    rw [mul, BitVec.ofNat_mul_ofNat, Nat.mul_comm]
  refine reshape ?_ rfl (by omega)
  rw [e1, e2, div_ofNat hmul hd, add, add, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat,
    Nat.add_comm (accum _ _ _ _), Nat.add_comm 1 (j + 1)]
  rfl

/-- From the head of the loop at byte 77, after `j` of the `m` steps, the loop ends.

It reaches byte 113 with the fee, for at most 49 gas and 87 more for each step left. -/
theorem feeLoop_head (hfork : .shapella ≤ fork) (hc : FeeLoopCode code) {x : U256} {d m : Nat}
    (hfits : FeeFits 1 d x.toNat m) (n : Nat) :
    ∀ j g, j + n = m → 49 + 87 * n ≤ g →
    Hoare fork (At code message 77 [BitVec.ofNat 256 (partialSum 1 x.toNat d j),
        BitVec.ofNat 256 (accum 1 x.toNat d j), BitVec.ofNat 256 (j + 1), x, BitVec.ofNat 256 d]
        memory g state substate returnData)
      (fun evm => ∃ g', g - (49 + 87 * n) ≤ g' ∧ At code message 113
        [BitVec.ofNat 256 (fakeExponential 1 x.toNat d)] memory g' state substate returnData
          evm) := by
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hfits
  have hd : d < 2 ^ 256 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right d (Nat.succ_pos m)) hf3
  intro j g hj hg
  have hcost : ∀ k, Triple.loopCost (fun _ => 87) k = 87 * k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Triple.loopCost, ih]; omega
  -- The invariant is at the head after `m - k` runs, or at byte 113 when the loop left early.
  refine Triple.consequence (Triple.loop_gas (S := Step fork)
    (I := fun k g evm => k ≤ n ∧ (At code message 77
        [BitVec.ofNat 256 (partialSum 1 x.toNat d (m - k)),
          BitVec.ofNat 256 (accum 1 x.toNat d (m - k)), BitVec.ofNat 256 (m - k + 1), x,
          BitVec.ofNat 256 d] memory g state substate returnData evm ∨
      ∃ g', g ≤ g' + (87 * k + 49) ∧ At code message 113
        [BitVec.ofNat 256 (fakeExponential 1 x.toNat d)] memory g' state substate returnData evm))
    (Q := fun g evm => ∃ g', g ≤ g' ∧ At code message 113
      [BitVec.ofNat 256 (fakeExponential 1 x.toNat d)] memory g' state substate returnData evm)
    (cost := fun _ => 87) (exitCost := 49) ?body ?exit n g (by rw [hcost]; omega))
    ?pre ?post
  · intro k g hk evm ⟨hkn, h⟩
    rcases h with h | ⟨g', hg', h⟩
    · by_cases hacc : accum 1 x.toNat d (m - (k + 1)) = 0
      · obtain ⟨after, hr, hq⟩ := feeLoop_exit hfork hc hacc
          (Nat.lt_of_le_of_lt (partialSum_le_of_le (by omega)) hf2) hd (by omega) evm h
        exact ⟨after, hr, by omega, Or.inr ⟨_, by omega, hq⟩⟩
      · obtain ⟨mid, hr, hq⟩ := feeLoop_body hfork hc hacc (hf4 _ (by omega))
          (Nat.lt_of_le_of_lt (partialSum_le_of_le (by omega)) hf2)
          (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left d (by omega)) hf3) (by omega) evm h
        exact ⟨mid, hr, by omega, Or.inl (by rw [show m - k = m - (k + 1) + 1 by omega]; exact hq)⟩
    · exact ⟨evm, .refl evm, by omega, Or.inr ⟨g', by omega, h⟩⟩
  · intro g hg evm ⟨_, h⟩
    rcases h with h | ⟨g', hg', h⟩
    · rw [Nat.sub_zero] at h
      obtain ⟨after, hr, hq⟩ := feeLoop_exit hfork hc hf1 hf2 hd hg evm h
      exact ⟨after, hr, _, Nat.le_refl _, hq⟩
    · exact ⟨evm, .refl evm, g', by omega, h⟩
  · exact fun evm h => ⟨Nat.le_refl _, Or.inl (by rw [show m - n = j by omega]; exact h)⟩
  · intro evm ⟨g', hg', h⟩
    refine ⟨g', ?_, h⟩
    simp only [hcost] at hg'
    omega

/-- From byte 69, the code computes the fee of the excess `x`, with the fraction `d`.

The loop of the fee stops within `m` steps with no overflow.

The run reaches byte 113 with the fee alone on the stack.

It pays at most 68 gas, and 87 more for each step. -/
theorem feeLoop (hfork : .shapella ≤ fork) (hc : FeeLoopCode code) {x : U256} {d m g : Nat}
    (hfits : FeeFits 1 d x.toNat m) (hg : 68 + 87 * m ≤ g) :
    Hoare fork (At code message 69 [x, BitVec.ofNat 256 d] memory g state substate returnData)
      (fun evm => ∃ g', g - (68 + 87 * m) ≤ g' ∧ At code message 113
        [BitVec.ofNat 256 (fakeExponential 1 x.toNat d)] memory g' state substate returnData
          evm) := by
  have hb := hc.byte
  have hp := hc.push
  have hl : ∀ i, i < 113 → i < code.size := fun i h => by have := hc.size; omega
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  evm_step [hb, hp, hl, FEE_LOOP_NUMBER]
  have e : mul (BitVec.ofNat 256 d) 1#256 = BitVec.ofNat 256 (accum 1 x.toNat d 0) := by
    rw [mul, BitVec.ofNat_mul_ofNat, accum, Nat.mul_comm]
  refine Triple.seq (reshape (s' := [BitVec.ofNat 256 (partialSum 1 x.toNat d 0),
    BitVec.ofNat 256 (accum 1 x.toNat d 0), BitVec.ofNat 256 (0 + 1), x, BitVec.ofNat 256 d])
    (by rw [e]; rfl) rfl rfl) ?_
  exact Triple.consequence (feeLoop_head hfork hc hfits m 0 _ (by omega) (by omega))
    (fun _ h => h) fun _ ⟨g', hg', h⟩ => ⟨g', by omega, h⟩

end FeeLoop

/-! ## Writes of the storage in the code -/

section Writes

open EthLib.Execution.Evm EthLib.Execution.Evm.Logic
open EthLib.Execution.Blocks.SystemContract (storageOf WritesStorage sloadPrice_le)

variable {fork : EthLib.Base.Fork} {code : ByteArray} {message : Message fork}
  {memory : ByteArray} {substate : Substate} {returnData : ByteArray}

/-- From Berlin, SSTORE writes `new` at the slot `key` with a conservative one-counter budget.

The frame may change the state, and the account of the contract exists.

The budget is 25,000 gas before Glamsterdam and 125,000 from Glamsterdam.

The write changes one slot and pays at most 22,100 gas times the storage-gas scale.

It keeps the logs. -/
theorem sstore_writes (hfork : .berlin ≤ fork) {pc : Nat}
    {key new : U256} {rest : List U256} {gas : Nat} {S : State.TransactionState}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x55) (hstatic : message.isStatic = false)
    (hacc : (S.getAccountOptional message.currentTarget).isSome = true)
    (hgas : 25000 * storageGasScale fork ≤ gas) :
    ∃ S', WritesStorage message.currentTarget
        (setSlot (storageOf S message.currentTarget) key new) S S' ∧
      Hoare fork (At code message pc (key :: new :: rest) memory gas S substate returnData)
        fun evm => ∃ g ss, gas ≤ g + 22100 * storageGasScale fork ∧ ss.logs = substate.logs ∧
          At code message (pc + 1) rest memory g S' ss returnData evm := by
  have hscale := one_le_storageGasScale fork
  have hcost := sstoreTotalCost_le hfork
    (S.getStorageOriginal message.currentTarget (U256.toBeBytes key))
    (S.getStorage message.currentTarget (U256.toBeBytes key)) new
    (decide (U256.toBeBytes key ∉ substate.accessedStorageKeys.getD message.currentTarget ∅))
  obtain ⟨S', hs, ho, -, ha, hc, -, h⟩ := sstore_of_account_total (code := code) (pc := pc)
    (gas := gas) (rest := rest) (key := key) (new := new) (memory := memory)
    (substate := substate) (returnData := returnData) hfork hlt hbyte hstatic rfl
    (by simp only [GasCosts.CALL_STIPEND]; omega) (by omega) hacc
  refine ⟨S', ⟨fun slot => ?_, fun o k hne => ho o k (.inl hne), ha, hc⟩,
    Triple.consequence h (fun _ h => h) fun evm h => by
      refine ⟨_, _, ?_, ?_, h⟩
      · omega
      · rfl⟩
  unfold storageOf setSlot
  by_cases hk : slot = key
  · subst hk
    simp only [ite_true]
    exact hs
  · simp only [hk, ite_false]
    exact ho _ _ (.inr fun e => hk (U256.toBeBytes_inj e))

/-- SSTORE of `new` at the slot `key`, followed by a specification from the frame after it.

It holds from each state that writes the slot, with the scaled write budget charged. -/
theorem sstore_then (hfork : .berlin ≤ fork) {pc : Nat}
    {key new : U256} {rest : List U256} {gas : Nat} {S : State.TransactionState}
    {Q : Evm fork Nat → Prop} (hlt : pc < code.size) (hbyte : code[pc] = 0x55)
    (hstatic : message.isStatic = false)
    (hacc : (S.getAccountOptional message.currentTarget).isSome = true)
    (hgas : 25000 * storageGasScale fork ≤ gas)
    (next : ∀ S', WritesStorage message.currentTarget
        (setSlot (storageOf S message.currentTarget) key new) S S' →
      (S'.getAccountOptional message.currentTarget).isSome = true → ∀ g ss,
      gas ≤ g + 22100 * storageGasScale fork → ss.logs = substate.logs →
      Spec fork (At code message (pc + 1) rest memory g S' ss returnData) Q) :
    Spec fork (At code message pc (key :: new :: rest) memory gas S substate returnData) Q := by
  obtain ⟨S', hw, h⟩ := sstore_writes (rest := rest) (memory := memory) (substate := substate)
    (returnData := returnData) hfork hlt hbyte hstatic hacc hgas
  exact Triple.seq h (Triple.of_gas_logs fun g ss hg hl =>
    next S' hw (by rw [hw.2.2.1]; exact hacc) g ss hg hl)

/-- From Berlin, SLOAD of the slot `key`, followed by a specification from the frame after it.

It pushes the word of the slot, records the read, and pays at most 2,100 gas. -/
theorem sload_then (hfork : .berlin ≤ fork) {pc : Nat} {key : U256} {rest : List U256}
    {gas : Nat} {S : State.TransactionState} {Q : Evm fork Nat → Prop}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x54) (hgas : 2100 ≤ gas)
    (next : ∀ g ss, gas ≤ g + 2100 → ss.logs = substate.logs →
      Spec fork (At code message (pc + 1) (storageOf S message.currentTarget key :: rest) memory g
        (S.recordStorageRead message.currentTarget (U256.toBeBytes key)) ss returnData) Q) :
    Spec fork (At code message pc (key :: rest) memory gas S substate returnData) Q := by
  have hp := sloadPrice_le (decide (U256.toBeBytes key ∉
    substate.accessedStorageKeys.getD message.currentTarget ∅))
  exact Triple.seq (sload hfork hlt hbyte rfl (Nat.le_trans hp hgas))
    (next _ _ (by omega) rfl)

/-- MSTORE of a word at the offset `t`, where memory of `s` bytes grows by `e` for 3 gas.

It is followed by a specification from the frame after it, with the new memory named. -/
theorem mstore_then {pc s t e : Nat} {start value : U256} {rest : List U256} {gas : Nat}
    {S : State.TransactionState} {Q : Evm fork Nat → Prop} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x52) (hs : memory.size = s) (ht : start.toNat = t)
    (hext : extendMemory s [(start, 32)] = ⟨3, e⟩) (hfit : t + 32 ≤ s + e) (hgas : 6 ≤ gas)
    (next : ∀ M, M = memoryWrite (memoryExtend memory e) t (wordBytes value) → M.size = s + e →
      Spec fork (At code message (pc + 1) rest M (gas - 6) S substate returnData) Q) :
    Spec fork (At code message pc (start :: value :: rest) memory gas S substate returnData) Q := by
  have h := mstore (start := start) (value := value) (rest := rest) (memory := memory)
    (gas := gas) (state := S) (substate := substate) (returnData := returnData)
    (message := message) hlt hbyte (by rw [hs, hext]; omega)
  rw [hs, hext, ht] at h
  refine Triple.seq h (next _ rfl ?_)
  rw [size_memoryWrite (by rw [size_memoryExtend, size_wordBytes, hs]; exact hfit),
    size_memoryExtend, hs]

/-- Growth of memory to at most 1,248 bytes costs at most 197 gas.

So the MSTORE that grows it costs at most 200. -/
theorem extendMemory_cost_le {size : Nat} {start : U256} (hmod : size % 32 = 0)
    (hend : start.toNat + 32 ≤ 1248) : (extendMemory size [(start, 32)]).cost ≤ 197 := by
  by_cases h : size < start.toNat + (32 : U256).toNat
  · rw [extendMemory_of_lt hmod (by decide) h]
    have hw : wordCount (ceil32 (start.toNat + (32 : U256).toNat)) ≤ 39 :=
      wordCount_le (ceil32_le (by decide) (by simpa using hend))
    have hsq := Nat.pow_le_pow_left hw 2
    simp only [memoryGasCost, GasCosts.MEMORY_PER_WORD]
    omega
  · rw [extendMemory_of_le (by omega)]
    decide

/-- MSTORE of a word that ends by byte 1,248, followed by a specification from the frame after it.

Memory grows by `e` bytes to a multiple of 32 that holds the word, for at most 200 gas. -/
theorem mstore_grow {code : ByteArray} {pc t : Nat} {start value : U256}
    {rest : List U256} {M : ByteArray} {gas : Nat} {S : State.TransactionState} {ss : Substate}
    {Q : Evm fork Nat → Prop} (hlt : pc < code.size) (hbyte : code[pc] = 0x52)
    (hmod : M.size % 32 = 0) (ht : start.toNat = t) (hend : t + 32 ≤ 1248) (hgas : 200 ≤ gas)
    (next : ∀ M' e g', M' = memoryWrite (memoryExtend M e) t (wordBytes value) →
      t + 32 ≤ M.size + e → M'.size = M.size + e → M'.size % 32 = 0 → gas ≤ g' + 200 →
      Spec fork (At code message (pc + 1) rest M' g' S ss returnData) Q) :
    Spec fork (At code message pc (start :: value :: rest) M gas S ss returnData) Q := by
  have hcost := extendMemory_cost_le (size := M.size) hmod (ht ▸ hend)
  refine Triple.seq (mstore hlt hbyte (by omega)) ?_
  have hsz := size_memoryExtend_extendMemory (memory := M) (start := start) (length := 32) hmod
    (by decide)
  rw [size_memoryExtend] at hsz
  have hc := ceil32_mod (start.toNat + (32 : U256).toNat)
  have hl := le_ceil32 (start.toNat + (32 : U256).toNat)
  have h32 : (32 : U256).toNat = 32 := rfl
  rw [ht]
  have hfit : t + 32 ≤ M.size + (extendMemory M.size [(start, 32)]).expandBy := by
    rw [hsz]
    omega
  have hs := size_memoryWrite
    (memory := memoryExtend M (extendMemory M.size [(start, 32)]).expandBy) (start := t)
    (value := wordBytes value) (by rw [size_memoryExtend, size_wordBytes]; exact hfit)
  rw [size_memoryExtend] at hs
  refine next _ _ _ rfl hfit hs ?_ (by omega)
  rw [hs, hsz]
  omega

end Writes

/-! ## What a stopped frame holds -/

section Frames

open EthLib.Execution.Evm EthLib.Execution.Evm.Logic
open EthLib.Execution.Blocks.SystemContract (storageOf WritesStorage)
open EthLib.Execution.State (TransactionState)
open EthLib.Base (Fork Address)

/-- What a stopped frame holds when a call adds the request `words` with the log data `data`.

The frame stops with no error and no output.

The state holds the storage after the request is added, at the contract, and keeps the rest.

The logs gain one log of the contract, with no topic and the data `data`.

The pseudocode of the EIP has no log; its code writes this one. -/
def Added {fork : Fork} (slots : Nat) (target : Address) (words : List U256) (data : ByteArray)
    (state : TransactionState) (substate : Substate) (evm : Evm fork Nat) : Prop :=
  evm.error = none ∧ evm.output = .empty ∧
    WritesStorage target (afterAdd slots words (storageOf state target)) state
      evm.state ∧
    evm.substate.logs = substate.logs.push { address := target, topics := [], data := data }

/-- Equal storages, keys and words give equal storages after the write. -/
theorem setSlot_congr {r r' : U256 → U256} {k k' v v' : U256} (hr : r = r') (hk : k = k')
    (hv : v = v') : setSlot r k v = setSlot r' k' v' := by
  rw [hr, hk, hv]

/-- A bound on the gas of the dequeue loop with `n` runs left: 9,000 per run, 30 for the exit. -/
def deqGas : Nat → Nat
  | 0 => 30
  | n + 1 => deqGas n + 9000

/-- What a stopped frame holds at the end of the system call, from the state `S`.

It stops with no error, returns `size` bytes of the memory `M`, and holds the storage `store`. -/
def Returned {fork : Fork} (target : Address) (M : ByteArray) (size : Nat)
    (store : U256 → U256) (S : TransactionState) (evm : Evm fork Nat) : Prop :=
  evm.error = none ∧ evm.output = memoryReadBytes M 0 size ∧ WritesStorage target store S evm.state

end Frames

/-! ## The bytes of a log -/

section LogBytes

open EthLib.Execution.Evm EthLib.Execution.Evm.Logic
open EthLib.Base (byteAt byteAt_append byteAt_extract natToBytes natToBytes_length natToBytes_mod)

/-- A word shifted up by 96 bits starts with the last 20 bytes of the word. -/
theorem byteAt_wordBytes_shl (c : U256) {i : Nat} (hi : i < 20) :
    byteAt (wordBytes (bitwiseShl 96#256 c)) i = byteAt (wordBytes c) (12 + i) := by
  have hw : (bitwiseShl 96#256 c).toNat / 256 ^ 12 = c.toNat % 256 ^ 20 := by
    simp only [bitwiseShl, BitVec.reduceToNat]
    rw [ite_eq_left (by decide), BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      show (2 : Nat) ^ 256 = 256 ^ 12 * 256 ^ 20 from rfl, Nat.mod_mul_right_div_self,
      show (2 : Nat) ^ 96 = 256 ^ 12 from rfl, Nat.mul_div_cancel _ (by decide)]
  rw [wordBytes_eq_append _ (show 20 + 12 = 32 from rfl), wordBytes_eq_append c
    (show 12 + 20 = 32 from rfl), byteAt_append, byteAt_append, hw, natToBytes_mod]
  have h1 : (⟨(natToBytes 20 c.toNat).toArray⟩ : ByteArray).size = 20 := by
    simp [ByteArray.size, natToBytes_length]
  have h2 : (⟨(natToBytes 12 (c.toNat / 256 ^ 20)).toArray⟩ : ByteArray).size = 12 := by
    simp [ByteArray.size, natToBytes_length]
  rw [h1, h2, ite_eq_left hi, ite_eq_right (by omega), Nat.add_sub_cancel_left]

/-- The mask of the code keeps the first 16 bytes of a word. -/
theorem byteAt_wordBytes_and (v : U256) {i : Nat} (hi : i < 16) :
    EthLib.Base.byteAt (wordBytes (bitwiseAnd
      0xffffffffffffffffffffffffffffffff00000000000000000000000000000000#256 v)) i =
      EthLib.Base.byteAt (wordBytes v) i := by
  have key : (bitwiseAnd
      0xffffffffffffffffffffffffffffffff00000000000000000000000000000000#256 v).toNat / 2 ^ 128 =
      v.toNat / 2 ^ 128 := by
    rw [toNat_bitwiseAnd, Nat.and_div_two_pow,
      show (0xffffffffffffffffffffffffffffffff00000000000000000000000000000000#256 : U256).toNat /
        2 ^ 128 = 2 ^ 128 - 1 from rfl, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by have := v.isLt; omega))
  rw [byteAt_wordBytes _ (by omega), byteAt_wordBytes _ (by omega),
    show 256 ^ (31 - i) = 2 ^ 128 * 256 ^ (15 - i) by
      rw [show 31 - i = 16 + (15 - i) by omega, Nat.pow_add],
    ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, key]

/-- The memory of a log of the caller and the input.

A word with the caller in its first 20 bytes is written at offset 0.

The input is then copied from offset 20.

The first `20 + n` bytes of memory are the 20 bytes of the caller, then the input. -/
theorem log_memory {c : U256} {data : ByteArray} {n e : Nat}
    (hn : data.size = n) (he : 20 + n ≤ 32 + e) :
    memoryReadBytes (memoryWrite (memoryExtend (wordBytes (bitwiseShl 96#256 c)) e) 20
      ⟨(bufferRead data 0 n).toArray⟩) 0 (20 + n) = (wordBytes c).extract 12 32 ++ data := by
  rw [show (⟨(bufferRead data 0 n).toArray⟩ : ByteArray) = data by
    subst hn; rw [bufferRead_zero_size]]
  have hs : (memoryExtend (wordBytes (bitwiseShl 96#256 c)) e).size = 32 + e := by
    rw [size_memoryExtend, size_wordBytes]
  have hA : Holds (memoryExtend (wordBytes (bitwiseShl 96#256 c)) e) 0
      ((wordBytes c).extract 12 32) := by
    refine Holds.of_byteAt (by simp [hs]; omega) fun i hi => ?_
    simp only [ByteArray.size_extract, size_wordBytes] at hi
    rw [Nat.zero_add, byteAt_memoryExtend, byteAt_wordBytes_shl c (by omega), byteAt_extract,
      size_wordBytes, ite_eq_left (by omega)]
  have hw : 20 + data.size ≤ (memoryExtend (wordBytes (bitwiseShl 96#256 c)) e).size := by
    rw [hs]; omega
  have h := (hA.memoryWrite_of_disjoint hw (by simp [size_wordBytes])).append
    (by simpa [size_wordBytes] using holds_memoryWrite hw)
  have := h.2
  simp only [ByteArray.size_append, ByteArray.size_extract, size_wordBytes] at this
  rw [← hn]
  simpa using this

end LogBytes

end EthLib.Execution.Blocks.RequestQueue
