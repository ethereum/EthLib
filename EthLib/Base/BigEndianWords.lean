module

public import EthLib.Base.BigEndian

/-!
# Big-endian conversion through 64-bit words

Eight bytes fit in a `UInt64`.

The reader supplies the words of a 32-byte block.

The writer appends words directly to a byte array.
-/

@[expose] public section

namespace EthLib.Base

/-- Append one byte at the low end of a word. -/
@[inline] def appendByte (word : UInt64) (byte : UInt8) : UInt64 :=
  word * 256 + byte.toUInt64

/-- Read eight bytes with the most significant byte first. -/
@[inline] def readWord (a b c d e f g h : UInt8) : UInt64 :=
  appendByte (appendByte (appendByte (appendByte
    (appendByte (appendByte (appendByte a.toUInt64 b) c) d) e) f) g) h

/-- Supply the four most-to-least significant words to a continuation. -/
@[inline] def withIndexedWords32 {α : Type} (byte : Fin 32 → UInt8)
    (use : UInt64 → UInt64 → UInt64 → UInt64 → α) : α :=
  let a := readWord (byte 0) (byte 1) (byte 2) (byte 3) (byte 4) (byte 5) (byte 6) (byte 7)
  let b := readWord (byte 8) (byte 9) (byte 10) (byte 11) (byte 12) (byte 13) (byte 14) (byte 15)
  let c := readWord (byte 16) (byte 17) (byte 18) (byte 19)
    (byte 20) (byte 21) (byte 22) (byte 23)
  let d := readWord (byte 24) (byte 25) (byte 26) (byte 27)
    (byte 28) (byte 29) (byte 30) (byte 31)
  use a b c d

/-- Supply the words read from a 32-byte block to a continuation. -/
@[inline] def withByteArrayWords32 {α : Type} (bytes : ByteArray) (start : Nat)
    (h : start + 32 ≤ bytes.size) (use : UInt64 → UInt64 → UInt64 → UInt64 → α) : α :=
  withIndexedWords32 (fun i => bytes[start + i.val]'(by omega)) use

/-- Append a word in big-endian order to an existing byte array. -/
@[inline] def pushWord64 (out : ByteArray) (w : UInt64) : ByteArray :=
  let a := w >>> 8
  let b := a >>> 8
  let c := b >>> 8
  let d := c >>> 8
  let e := d >>> 8
  let f := e >>> 8
  let g := f >>> 8
  out.push g.toUInt8 |>.push f.toUInt8 |>.push e.toUInt8 |>.push d.toUInt8
    |>.push c.toUInt8 |>.push b.toUInt8 |>.push a.toUInt8 |>.push w.toUInt8

/-- Append 32 big-endian bytes directly to a byte array. -/
@[inline] def pushNatBytes32 (out : ByteArray) (n : Nat) : ByteArray :=
  let out := pushWord64 out (n >>> 192).toUInt64
  let out := pushWord64 out (n >>> 128).toUInt64
  let out := pushWord64 out (n >>> 64).toUInt64
  pushWord64 out n.toUInt64

end EthLib.Base
