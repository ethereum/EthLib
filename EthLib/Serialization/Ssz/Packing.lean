module

public import EthLib.Base.ByteOrder
public import EthLib.Serialization.Ssz.Error

/-! Byte encodings shared by SSZ serialization and merkleization. -/

@[expose] public section

namespace EthLib.Serialization.Ssz

/--
An unsigned integer as little-endian bytes of the given width.

A value wider than the given width is truncated.

A caller needing exact recovery has to check the range itself.
-/
def uintBytes (width value : Nat) : Bytes := ⟨(Base.ByteOrder.toLE width value).toArray⟩

/-- The eight bits that land in one byte, gathered into it. -/
def packByte (bits : Array Bool) (byteIndex : Nat) : UInt8 :=
  let held (offset : Nat) : UInt8 :=
    -- Bit `i` of the value is bit `i mod 8` of byte `floor(i / 8)`.
    --
    -- So bit `offset` of byte `b` holds bit `i = 8 * b + offset` of the value.
    --
    -- An absent bit contributes zero, which is also the high padding of the last byte.
    if bits[byteIndex * 8 + offset]?.getD false then (1 : UInt8) <<< UInt8.ofNat offset else 0
  held 0 ||| held 1 ||| held 2 ||| held 3 ||| held 4 ||| held 5 ||| held 6 ||| held 7

/--
Bits packed into bytes, the first bit lowest in the first byte.

For example, the bits 1, 0, 1, 1 give the byte `0b00001101`.

Each byte is built from the bits that land in it, rather than one bit at a time into a buffer.

A byte then stands on its own, which is what lets a bit be read back where it was put.
-/
def packBits (bits : Array Bool) (byteCount : Nat) : Bytes :=
  ⟨Array.ofFn (n := byteCount) fun byteIndex => packByte bits byteIndex.val⟩

end EthLib.Serialization.Ssz
