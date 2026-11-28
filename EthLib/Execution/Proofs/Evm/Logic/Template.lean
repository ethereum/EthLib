module

public import EthLib.Execution.Proofs.Evm.Logic.Region
public import EthLib.Execution.Proofs.Evm.Logic.NatCode
import EthLib.Execution.Proofs.Evm.Machine.Memory

/-!
# Proofs: blocks of bytes at an offset of a code

A large code repeats a few shapes of blocks, at many offsets and with different constants.

A template lemma proves one shape once, for every code that holds its bytes at any offset.

Each use then needs only that the code holds the bytes, which the kernel checks on its number.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork byteAtOrZero)

variable {code bytes : ByteArray} {o : Nat}

namespace Holds

/-- Each byte of a block that the code holds lies inside the code. -/
theorem lt (h : Holds code o bytes) {i : Nat} (hi : i < bytes.size) : o + i < code.size := by
  have := h.1
  omega

/-- Each byte of the code in a block that it holds is the byte of the block. -/
theorem getElem (h : Holds code o bytes) {i : Nat} (hi : i < bytes.size) :
    code[o + i]'(h.lt hi) = bytes[i] := by
  have := h.byteAtOrZero_eq hi
  simp only [byteAtOrZero, h.lt hi, hi, ↓reduceDIte] at this
  exact this

/-- The `k` bytes after the index `i` of a block, read as the data of a PUSH at `i`.

They are the big-endian number of those bytes of the block. -/
theorem pushData (h : Holds code o bytes) {i k : Nat} (hk : i + k < bytes.size) :
    EthLib.Execution.Evm.pushData code (o + i) k =
      BitVec.ofNat 256 (EthLib.Base.ByteOrder.ofBE ((bytes.data.toList.drop (i + 1)).take k)) := by
  unfold EthLib.Execution.Evm.pushData
  rw [bufferRead_eq]
  congr 2
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take, List.length_drop,
      Array.length_toList]
    have : bytes.data.size = bytes.size := rfl
    omega
  · intro j h₁ h₂
    simp only [List.length_map, List.length_range] at h₁
    simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop,
      Array.getElem_toList]
    rw [show o + i + 1 + j = o + (i + 1 + j) by omega, h.byteAtOrZero_eq (by omega)]
    simp only [byteAtOrZero, show i + 1 + j < bytes.size by omega, ↓reduceDIte]
    rfl

end Holds

/-- Whether the code stored in `n` holds `bytes` from `o` on, by one evaluation of its bytes.

The kernel checks it with `decide +kernel`.

Its cost grows with the block and the size of the code, not with the offset. -/
def holdsNat (n size o : Nat) (bytes : ByteArray) : Bool :=
  decide (o + bytes.size ≤ size) &&
    (List.range bytes.size).all fun i => NatCode.natByte n size (o + i) == byteAtOrZero bytes i

/-- The code stored in a number holds a block when the check on its number passes. -/
theorem holds_ofNat {n size : Nat} (h : holdsNat n size o bytes = true) :
    Holds (NatCode.ofNat n size) o bytes := by
  simp only [holdsNat, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at h
  obtain ⟨hsize, hall⟩ := h
  refine Holds.of_byteAtOrZero (by rw [NatCode.size_ofNat]; exact hsize) fun i hi => ?_
  rw [NatCode.byteAtOrZero_ofNat]
  exact hall i hi

/-- Whether the code stored in `n` holds `k` blocks, the block `block j` at `o + len * j`.

The blocks start every `len` bytes.

Nothing ties `len` to their sizes.

One kernel check covers every copy of a repeated block. -/
def holdsRep (n size o len : Nat) (block : Nat → ByteArray) : (k : Nat) → Bool
  | 0 => true
  | k + 1 => holdsNat n size (o + len * k) (block k) && holdsRep n size o len block k

/-- The code stored in a number holds each of the blocks that the check on its number covers. -/
theorem holds_ofRep {n size len : Nat} {block : Nat → ByteArray} :
    ∀ {k : Nat}, holdsRep n size o len block k = true →
      ∀ j, j < k → Holds (NatCode.ofNat n size) (o + len * j) (block j)
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | k + 1, h, j, hj => by
    simp only [holdsRep, Bool.and_eq_true] at h
    by_cases hjk : j = k
    · subst hjk
      exact holds_ofNat h.1
    · exact holds_ofRep h.2 j (by omega)

/-! ## A proof of a large code across files

- One file states the code as words, with `ofWords`, and runs the kernel checks once.
- Each check covers a repeated block, a single block, or the jump destinations from one walk.
- Template lemmas prove each shape of block at an abstract code, so no step unfolds the code.
- Range files compose the template lemmas over their part of the code, by the chain below.
- A last file joins the ranges at the code itself.
-/

namespace Triple

variable {fork : Fork} {Meter : Type} {S : Evm fork Meter → Evm fork Meter → Prop}

/-- A chain of `k` triples, each from the frames of `F j` to those of `F (j + 1)`.

It composes `k` copies of a block, each proved by one template lemma. -/
theorem chain {F : Nat → Evm fork Meter → Prop} :
    ∀ {k : Nat}, (∀ j, j < k → Triple S (F j) (F (j + 1))) → Triple S (F 0) (F k)
  | 0, _ => of_imp fun _ h => h
  | k + 1, step => (chain fun j hj => step j (by omega)).seq (step k (by omega))

end Triple

end EthLib.Execution.Evm.Logic
