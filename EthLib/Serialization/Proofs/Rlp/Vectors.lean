import EthLib.Serialization.Rlp.Item

/-!
# `Serialization.Proofs.Rlp.Vectors`

How the known answers write their bytes and items, so that the kernel evaluates them in little memory.
-/

namespace EthLib.Serialization.Rlp.Vectors

/-- A byte string written as text: the UTF-8 bytes of the text, one byte per ASCII character. -/
def str (text : String) : Item :=
  .bytes text.toUTF8

/-- A long byte string written as text in pieces: the UTF-8 bytes of the pieces, one after another.

The kernel's cost to turn a string into bytes grows with the square of its length.

In one string, the 1024 characters of `longstring2` take it more than 4 GB of memory.

In pieces of at most 64 characters, they take it less than 0.5 GB. -/
def strPieces (pieces : List String) : Item :=
  .bytes ⟨⟨pieces.flatMap (·.toUTF8.data.toList)⟩⟩

/-- `value` in base 256 on exactly `size` bytes, most significant first.

Each expected byte string is the hex number its source gives, after its byte count.

The count keeps a leading zero byte, as in the output `00`.

A value too large for its count gives the empty list, so a claim on it fails instead of comparing fewer bytes.

The kernel computes these bytes with its fast arithmetic on natural numbers.

Reading the same hex from a string costs it far more. -/
def bytesOf (size value : Nat) : List UInt8 :=
  if value < 256 ^ size then go size value [] else []
where
  /-- The lowest `size` digits of `value`, in front of `acc`. -/
  go : Nat → Nat → List UInt8 → List UInt8
    | 0, _, acc => acc
    | size + 1, value, acc => go size (value / 256) (UInt8.ofNat (value % 256) :: acc)

/-- The byte array of `value` on exactly `size` bytes, most significant first. -/
def byteArrayOf (size value : Nat) : ByteArray :=
  ⟨⟨bytesOf size value⟩⟩

end EthLib.Serialization.Rlp.Vectors
