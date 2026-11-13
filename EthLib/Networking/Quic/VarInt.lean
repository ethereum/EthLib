module

public import EthLib.Base.BigEndian

/-!
# QUIC variable-length integers

[RFC 9000 §16][rfc] encodes a value below `2^62` in 1, 2, 4 or 8 bytes.

The first two bits select the length, and the remaining bits hold a big-endian integer.

The decoder accepts longer forms too, as §16 permits outside frame types.

[rfc]: https://www.rfc-editor.org/rfc/rfc9000#section-16
-/

@[expose] public section

namespace EthLib.Networking.Quic

open EthLib.Base

/-- A QUIC integer, bounded by RFC 9000 §16. -/
abbrev VarInt := Fin (2 ^ 62)

namespace VarInt

/-- The two-bit length selector of RFC 9000 §16, Table 4. -/
abbrev Width := Fin 4

/-- The bytes after the first byte, for a length selector. -/
def tailLength (width : Width) : Nat := 2 ^ width.val - 1

/-- The first value that does not fit this width's payload bits. -/
def capacity (width : Width) : Nat := 64 * 256 ^ tailLength width

/-- Reasons to reject a QUIC integer at the encoding boundary. -/
inductive Error where
  /-- The selected width cannot hold the value. -/
  | tooLarge
  /-- The input ends before the selected integer does. -/
  | truncated
  deriving Repr, DecidableEq

/-- One stable code per kind of integer error. -/
def Error.code : Error → UInt32
  | .tooLarge => 1
  | .truncated => 2

/-- Write a chosen width, including a longer form, as RFC 9000 §16 permits.

The proof that the value fits prevents truncation by the big-endian writer. -/
def encodeWith (width : Width) (value : VarInt) (_ : value.val < capacity width) : List UInt8 :=
  UInt8.ofNat (width.val * 64 + value.val / 256 ^ tailLength width) ::
    natToBytes (tailLength width) value.val

/-- The shortest width that holds a value, required for frame types by RFC 9000 §12.4. -/
def width (value : VarInt) : Width :=
  if value.val < 64 then 0
  else if value.val < 16384 then 1
  else if value.val < 1073741824 then 2
  else 3

/-- The selected width holds every bit of the value. -/
theorem lt_capacity_width (value : VarInt) : value.val < capacity (width value) := by
  unfold width
  split
  · simpa [capacity, tailLength] using ‹value.val < 64›
  · split
    · simpa [capacity, tailLength] using ‹value.val < 16384›
    · split
      · simpa [capacity, tailLength] using ‹value.val < 1073741824›
      · exact value.isLt

/-- Write the shortest representation of a QUIC integer. -/
def encode (value : VarInt) : List UInt8 :=
  encodeWith (width value) value (lt_capacity_width value)

/-- Read one integer, returning the bytes after it and accepting longer representations.

RFC 9000 §16 gives the length in the high two bits of the first byte. -/
def decode : List UInt8 → Except Error (VarInt × List UInt8)
  | [] => .error .truncated
  | head :: rest =>
    let selector : Width := ⟨head.toNat / 64, by have := head.toNat_lt; omega⟩
    let count := tailLength selector
    if rest.length < count then .error .truncated
    else
      let value := head.toNat % 64 * 256 ^ count + bytesToNat (rest.take count)
      if h : value < 2 ^ 62 then .ok (⟨value, h⟩, rest.drop count)
      else .error .tooLarge

end VarInt
end EthLib.Networking.Quic
