module

public import EthLib.Execution.Proofs.Evm.Logic.Template
public import EthLib.Execution.Proofs.Evm.Logic.Steps
import EthLib.Base.Proofs.ByteOrder
import EthLib.Execution.Proofs.Evm.Machine.Memory

/-!
# Proofs: a block of code at any offset, with its jump targets moved

A compiler can place the same function at different offsets of different codes.

The bytes of the copies differ only in the PUSH2 data that name positions inside the function.

Each such datum is the position in the block plus the offset of the block.

A proof at an abstract code and offset covers every copy, and steps at `o + k`.

One kernel check on the number of each concrete code gives its copy.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (byteAtOrZero)

/-- The code holds `block` from offset `o`, with the jump targets of the block moved by `o`.

The masks are numbers whose bit `i` speaks of the byte `i` of the block.

- A byte marked in `fixed` is the byte of the block.
- The two bytes after a position marked in `reloc` read as their number in the block plus `o`.
- A position marked in `dest` is a valid jump destination once moved by `o`. -/
structure Relocated (code : ByteArray) (o : Nat) (block : ByteArray) (fixed reloc dest : Nat) :
    Prop where
  /-- The block lies inside the code. -/
  fit : o + block.size ≤ code.size
  /-- Every position in the block is a number that a word holds. -/
  lt_word : o + block.size < 2 ^ 256
  /-- Each fixed byte is the byte of the block. -/
  byte : ∀ i, i < block.size → fixed >>> i % 2 = 1 →
    byteAtOrZero code (o + i) = byteAtOrZero block i
  /-- The two bytes after a marked position read as their number in the block plus `o`. -/
  push : ∀ i, i + 2 < block.size → reloc >>> i % 2 = 1 →
    pushData code (o + i) 2 = BitVec.ofNat 256 (o + (pushData block i 2).toNat)
  /-- Each marked position is a valid jump destination of the code, moved by `o`. -/
  dest : ∀ i, i < block.size → dest >>> i % 2 = 1 →
    isValidJumpDest (validJumpDestinations code) (o + i) = true

namespace Relocated

variable {code block : ByteArray} {o fixed reloc dest : Nat}

/-- A position in the block lies inside the code. -/
theorem lt (h : Relocated code o block fixed reloc dest) {i : Nat} (hi : i < block.size) :
    o + i < code.size := by
  have := h.fit
  omega

/-- A byte of the code in the block: the byte of the block when it is fixed.

The condition is closed for a number `i`, so a rewrite evaluates it and takes one branch. -/
theorem getElem_ite (h : Relocated code o block fixed reloc dest) {i : Nat}
    (hlt : o + i < code.size) :
    code[o + i] = if fixed >>> i % 2 = 1 ∧ i < block.size then byteAtOrZero block i
      else byteAtOrZero code (o + i) := by
  split
  · next hc =>
    rw [← h.byte i hc.2 hc.1]
    simp only [byteAtOrZero, hlt, ↓reduceDIte]
  · simp only [byteAtOrZero, hlt, ↓reduceDIte]

/-- Each of the `k` bits of a mask from bit `s` is set when those bits read as all ones. -/
private theorem bit_of_mod {m s k j : Nat} (hm : (m >>> s) % 2 ^ k = 2 ^ k - 1) (hj : j < k) :
    m >>> (s + j) % 2 = 1 := by
  have hb := congrArg (fun x => Nat.testBit x j) hm
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight, hj,
    decide_true, Bool.true_and] at hb
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at hb
  rw [Nat.shiftRight_eq_div_pow]
  exact hb

/-- The data of a PUSH whose bytes are all fixed is the data of the block. -/
theorem pushData_eq (h : Relocated code o block fixed reloc dest) {i k : Nat}
    (hi : i + k < block.size) (hf : (fixed >>> (i + 1)) % 2 ^ k = 2 ^ k - 1) :
    pushData code (o + i) k = pushData block i k := by
  unfold pushData
  rw [bufferRead_eq, bufferRead_eq]
  congr 2
  refine List.map_congr_left fun j hj => ?_
  have hj : j < k := List.mem_range.mp hj
  rw [show o + i + 1 + j = o + (i + 1 + j) by omega]
  exact h.byte _ (by omega) (bit_of_mod hf hj)

/-- The data of a PUSH in the block, by its masks.

Fixed data is the data of the block, and a relocated PUSH2 pushes the data of the block plus `o`.

Both conditions are closed for numbers `i` and `k`, so a rewrite evaluates them.

Otherwise the data is read from the code, so a rewrite never meets the left side again. -/
theorem pushData_ite (h : Relocated code o block fixed reloc dest) {i k : Nat} :
    pushData code (o + i) k =
      if i + k < block.size ∧ (fixed >>> (i + 1)) % 2 ^ k = 2 ^ k - 1 then pushData block i k
      else if i + 2 < block.size ∧ reloc >>> i % 2 = 1 ∧ k = 2 then
        BitVec.ofNat 256 (o + (pushData block i 2).toNat)
      else BitVec.ofNat 256 (EthLib.Base.ByteOrder.ofBE (bufferRead code (o + i + 1) k)) := by
  split
  · next hc => exact h.pushData_eq hc.1 hc.2
  · split
    · next hc =>
      obtain ⟨h1, h2, rfl⟩ := hc
      exact h.push i h1 h2
    · rfl

/-- A position in the block, pushed as a word, reads back as itself. -/
theorem toNat_ofNat (h : Relocated code o block fixed reloc dest) {i : Nat}
    (hi : i < block.size) : (BitVec.ofNat 256 (o + i)).toNat = o + i := by
  have := h.lt_word
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- A marked position in the block, pushed as a word, is a valid jump destination. -/
theorem valid (h : Relocated code o block fixed reloc dest) {i : Nat}
    (hd : dest >>> i % 2 = 1) (hi : i < block.size) :
    isValidJumpDest (validJumpDestinations code) (BitVec.ofNat 256 (o + i)).toNat = true := by
  rw [h.toNat_ofNat hi]
  exact h.dest i hi hd

/-- The first position of the block lies inside the code. -/
theorem lt_zero (h : Relocated code o block fixed reloc dest) (hi : 0 < block.size) :
    o < code.size := by
  simpa using h.lt hi

/-- The first byte of the code in the block, at `o` itself. -/
theorem getElem_ite_zero (h : Relocated code o block fixed reloc dest) (hlt : o < code.size) :
    code[o] = if fixed % 2 = 1 ∧ 0 < block.size then byteAtOrZero block 0
      else byteAtOrZero code o := by
  have := h.getElem_ite (i := 0) (by simpa using hlt)
  simpa using this

/-- The data of a PUSH at the first byte of the block, at `o` itself. -/
theorem pushData_ite_zero (h : Relocated code o block fixed reloc dest) {k : Nat} :
    pushData code o k =
      if k < block.size ∧ (fixed >>> 1) % 2 ^ k = 2 ^ k - 1 then pushData block 0 k
      else if 2 < block.size ∧ reloc % 2 = 1 ∧ k = 2 then
        BitVec.ofNat 256 (o + (pushData block 0 2).toNat)
      else BitVec.ofNat 256 (EthLib.Base.ByteOrder.ofBE (bufferRead code (o + 1) k)) := by
  have := h.pushData_ite (i := 0) (k := k)
  simpa using this

/-- The first position of the block, pushed as a word, reads back as itself. -/
theorem toNat_ofNat_zero (h : Relocated code o block fixed reloc dest) (hi : 0 < block.size) :
    (BitVec.ofNat 256 o).toNat = o := by
  simpa using h.toNat_ofNat hi

/-- The first position of the block, pushed as a word and marked, is a valid jump destination. -/
theorem valid_zero (h : Relocated code o block fixed reloc dest) (hd : dest % 2 = 1)
    (hi : 0 < block.size) :
    isValidJumpDest (validJumpDestinations code) (BitVec.ofNat 256 o).toNat = true := by
  simpa using h.valid (i := 0) (by simpa using hd) hi

end Relocated

/-- Whether the code stored in `n` holds the block stored in `b` from `o`, relocated.

The block has `bsize` bytes, stored as a number as the code is.

The kernel checks it with `decide +kernel`, once for each concrete code.

The valid jump destinations come from the walk along the opcodes of the code. -/
def relocatedNat (n size o b bsize fixed reloc dest : Nat) : Bool :=
  decide (o + bsize ≤ size) && decide (o + bsize < 2 ^ 256) &&
    (List.range bsize).all fun i =>
      -- A fixed byte is the byte of the block.
      (fixed >>> i % 2 != 1 || NatCode.natByte n size (o + i) == NatCode.natByte b bsize i) &&
      -- A relocated PUSH2 holds its datum in the block plus `o`, as two big-endian bytes.
      (reloc >>> i % 2 != 1 || (decide (i + 2 < bsize) &&
        (NatCode.natByte n size (o + i + 1)).toNat * 256 +
            (NatCode.natByte n size (o + i + 2)).toNat ==
          o + ((NatCode.natByte b bsize (i + 1)).toNat * 256 +
            (NatCode.natByte b bsize (i + 2)).toNat))) &&
      -- A marked position is a valid jump destination, moved by `o`.
      (dest >>> i % 2 != 1 || (NatCode.jumpDests n size).contains (o + i))

/-- Two bytes of code read as a PUSH2 datum are their big-endian number. -/
private theorem pushData_two (code : ByteArray) (pc : Nat) :
    pushData code pc 2 = BitVec.ofNat 256
      ((byteAtOrZero code (pc + 1)).toNat * 256 + (byteAtOrZero code (pc + 1 + 1)).toNat) := by
  unfold pushData
  rw [bufferRead_eq]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.singleton_append,
    List.map_cons, List.map_nil, Nat.add_zero, EthLib.Base.ByteOrder.ofBE_cons,
    EthLib.Base.ByteOrder.ofBE_nil]
  congr 1
  simp only [List.length_cons, List.length_nil]
  omega

/-- The code stored in a number holds a relocated block when the check on its number passes. -/
theorem relocated_ofNat {n size o b bsize fixed reloc dest : Nat}
    (h : relocatedNat n size o b bsize fixed reloc dest = true) :
    Relocated (NatCode.ofNat n size) o (NatCode.ofNat b bsize) fixed reloc dest := by
  simp only [relocatedNat, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨hfit, hword⟩, hall⟩ := h
  have hb : ∀ m s j, byteAtOrZero (NatCode.ofNat m s) j = NatCode.natByte m s j :=
    NatCode.byteAtOrZero_ofNat
  refine ⟨by rw [NatCode.size_ofNat, NatCode.size_ofNat]; exact hfit,
    by rw [NatCode.size_ofNat]; exact hword, fun i hi hf => ?_, fun i hi hr => ?_,
    fun i hi hd => ?_⟩ <;> rw [NatCode.size_ofNat] at hi
  · have := (hall i hi).1.1
    simp only [hf, bne_self_eq_false, Bool.false_or, beq_iff_eq] at this
    rw [hb, hb, this]
  · have := (hall i (by omega)).1.2
    simp only [hr, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at this
    have h1 := (NatCode.natByte b bsize (i + 1)).toNat_lt
    have h2 := (NatCode.natByte b bsize (i + 1 + 1)).toNat_lt
    simp only [Nat.reducePow] at h1 h2
    rw [pushData_two, pushData_two, hb, hb, hb, hb, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), show o + i + 1 + 1 = o + i + 2 by omega,
      show i + 1 + 1 = i + 2 by omega, this.2]
  · have := (hall i hi).2
    simp only [hd, bne_self_eq_false, Bool.false_or, List.contains_iff_mem] at this
    exact NatCode.isValidJumpDest_ofNat_iff.mpr this

/-! ## Steps over a relocated block

Each tactic takes a proof `h` that the code holds a relocated block, and rules `ls` that unfold
the block and its masks into numbers.
-/

open Lean.Parser.Tactic

/-- Proves a fact about a relocated code at a position `o + k`, from `h` and the rules `ls`.

The fact is that the position lies inside the code, the byte there, or the data of a PUSH. -/
syntax "evm_codeR " term:max " [" simpLemma,* "]" : tactic

macro_rules
  | `(tactic| evm_codeR $h [$ls,*]) => `(tactic| evm_code [$ls,*, Relocated.lt $h,
      Relocated.lt_zero $h,
      Relocated.getElem_ite $h, Relocated.pushData_ite $h, Relocated.getElem_ite_zero $h,
      Relocated.pushData_ite_zero $h, NatCode.byteAtOrZero_ofNat, and_self,
      and_true, true_and, and_false, false_and, eq_self_iff_true, Nat.reduceEqDiff])

/-- Proves that a jump destination of a relocated code is valid.

The destination is a hypothesis, or a position of the block that its mask marks. -/
syntax "evm_destR " term:max " [" simpLemma,* "]" : tactic

macro_rules
  | `(tactic| evm_destR $h [$ls,*]) => `(tactic| first
      -- At reducible transparency: unfolding `o + k` against a hypothesis recurses `k` times.
      | with_reducible assumption
      -- The simprocs evaluate the masks and the sizes: `decide` would shift a mask bit by bit.
      | exact Relocated.valid $h
          (by first | (simp only [$ls,*, Nat.reduceShiftRight, Nat.reduceMod]; done) | decide)
          (by first | (simp only [$ls,*, NatCode.size_ofNat, Nat.reduceLT]; done) | decide)
      | exact Relocated.valid_zero $h
          (by first | (simp only [$ls,*, Nat.reduceMod]; done) | decide)
          (by first | (simp only [$ls,*, NatCode.size_ofNat, Nat.reduceLT]; done) | decide))

/-- Runs the opcode at the program counter `o + k` of a relocated code, by its rule.

It steps as on a frame that knows a few ranges of memory, with the code facts from `h`.

A jump to a position of the block, or to a destination that a hypothesis proves valid, comes
back at `o + k` too. -/
syntax "evm_stepR " term:max " [" simpLemma,* "]" : tactic

macro_rules
  | `(tactic| evm_stepR $h [$ls,*]) => `(tactic| first
      | evm_stepK [$ls,*, Relocated.lt $h, Relocated.lt_zero $h, Relocated.getElem_ite $h,
          Relocated.pushData_ite $h, Relocated.getElem_ite_zero $h, Relocated.pushData_ite_zero $h,
          NatCode.byteAtOrZero_ofNat, and_self, and_true, true_and, and_false, false_and,
          eq_self_iff_true, Nat.reduceEqDiff]
      -- JUMP and a taken JUMPI, whose destination the code facts alone do not prove valid.
      | ((refine' Triple.seq (Known.of_at fun _ => ?step) ?next
          case step => (first
            | (refine' Triple.seq (jump ?lt ?op ?gas ?dest) ?n
               case lt => evm_codeR $h [$ls,*]
               case op => evm_codeR $h [$ls,*]
               case gas => evm_gas
               case dest => evm_destR $h [$ls,*])
            | (refine' Triple.seq (jumpi_taken ?lt ?op ?gas ?nz ?dest) ?n
               case lt => evm_codeR $h [$ls,*]
               case op => evm_codeR $h [$ls,*]
               case gas => evm_gas
               case nz => first | evm_decide | with_reducible assumption
               case dest => evm_destR $h [$ls,*])) <;> evm_tidy <;>
            exact Triple.of_imp fun _ h => h)
         -- The destination, a position of the block pushed as a word, reads back as `o + k`.
         <;> evm_tidyK <;> (try simp only [Relocated.toNat_ofNat $h,
           Relocated.toNat_ofNat_zero $h, $ls,*, NatCode.size_ofNat, Nat.reduceLT])))

end EthLib.Execution.Evm.Logic
