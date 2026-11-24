module

public import EthLib.Base.Proofs.ByteOrder
public import EthLib.Serialization.Ssz.Packing

/-! The widths and bit positions of the byte encodings shared by SSZ codecs and trees. -/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- An integer of no bytes is written as nothing. -/
theorem uintBytes_zero (value : Nat) : uintBytes 0 value = #[] := rfl

/-- An integer is written as its low byte, then its quotient by 256 one byte narrower. -/
theorem uintBytes_succ (width value : Nat) :
    uintBytes (width + 1) value
      = #[UInt8.ofNat (value % 256)] ++ uintBytes width (value / 256) := by
  -- A byte keeps only the value modulo 256 anyway.
  rw [uintBytes, uintBytes, Base.ByteOrder.toArray_toLE_succ, ← UInt8.ofNat_mod_size (x := value)]

/-- An integer takes exactly the width it was written at. -/
theorem uintBytes_size (width value : Nat) : (uintBytes width value).size = width := by
  -- The value shrinks by a factor of 256 at every step, so it stays quantified over.
  induction width generalizing value with
  -- No bytes were asked for, and none were written.
  | zero => rfl
  -- One byte was written and the rest is the same claim one width down.
  | succ width ih => simp only [uintBytes_succ, Array.size_append, Array.size_singleton, ih]; omega

/--
Every bit reads back where it was put, and no other bit of the byte disturbs it.

A byte holds eight bits, and the offset selects one of them.

The remaining bits form a finite check.
-/
theorem packByte_bit (bits : Array Bool) (byteIndex offset : Nat) (small : offset < 8) :
    ((packByte bits byteIndex >>> UInt8.ofNat offset) &&& 1 == 1)
      = bits[byteIndex * 8 + offset]?.getD false := by
  -- The offset is one of eight, so it is made concrete before anything is named.
  match offset, small with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp only [packByte]
    -- The eight bits of this byte are arbitrary, so they are named and the rest decided.
    generalize bits[byteIndex * 8 + 0]?.getD false = b0
    generalize bits[byteIndex * 8 + 1]?.getD false = b1
    generalize bits[byteIndex * 8 + 2]?.getD false = b2
    generalize bits[byteIndex * 8 + 3]?.getD false = b3
    generalize bits[byteIndex * 8 + 4]?.getD false = b4
    generalize bits[byteIndex * 8 + 5]?.getD false = b5
    generalize bits[byteIndex * 8 + 6]?.getD false = b6
    generalize bits[byteIndex * 8 + 7]?.getD false = b7
    revert b0 b1 b2 b3 b4 b5 b6 b7
    decide

end EthLib.Serialization.Ssz
