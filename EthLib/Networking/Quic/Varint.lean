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

/-- A QUIC integer: a value below `2^62`, RFC 9000 §16. -/
abbrev Varint := Fin (2 ^ 62)

namespace Varint

/-- The two-bit length selector of RFC 9000 §16, Table 4. -/
abbrev Width := Fin 4

/-- The number of bytes after the first byte: 0, 1, 3 or 7. -/
def tailLength (width : Width) : Nat := 2 ^ width.val - 1

/-- The first value that this width cannot hold: `2^6`, `2^14`, `2^30` or `2^62`. -/
def capacity (width : Width) : Nat := 64 * 256 ^ tailLength width

/-- Every width carries at most 62 payload bits. -/
theorem capacity_le (width : Width) : capacity width ≤ 2 ^ 62 := by
  rcases width with ⟨w, hw⟩
  have : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;>
    dsimp only [capacity, tailLength] <;> decide

/-- Reasons to reject the bytes of a QUIC integer. -/
inductive VarintError where
  /-- The input ends before the selected integer does. -/
  | truncated
  deriving Repr, DecidableEq

/-- One stable code per kind of integer error. -/
def VarintError.code : VarintError → UInt32
  | .truncated => 1

/-- Write a value at a chosen width, a longer form included.

RFC 9000 §16 permits a longer form everywhere except in frame types.

The value must be below the width's capacity, so its high bits fit under the two selector bits. -/
def encodeWith (width : Width) (value : Varint) (_ : value.val < capacity width) : List UInt8 :=
  UInt8.ofNat (width.val * 64 + value.val / 256 ^ tailLength width) ::
    natToBytes (tailLength width) value.val

/-- The shortest width that holds a value, required for frame types by RFC 9000 §12.4. -/
def minWidth (value : Varint) : Width :=
  if value.val < 64 then 0
  else if value.val < 16384 then 1
  else if value.val < 1073741824 then 2
  else 3

/-- The shortest width holds every bit of the value. -/
theorem lt_capacity_minWidth (value : Varint) : value.val < capacity (minWidth value) := by
  unfold minWidth
  split
  · simpa [capacity, tailLength] using ‹value.val < 64›
  · split
    · simpa [capacity, tailLength] using ‹value.val < 16384›
    · split
      · simpa [capacity, tailLength] using ‹value.val < 1073741824›
      · exact value.isLt

/-- Write the shortest representation of a QUIC integer. -/
def encode (value : Varint) : List UInt8 :=
  encodeWith (minWidth value) value (lt_capacity_minWidth value)

/-- The width that the high two bits of a first byte select. -/
def selector (head : UInt8) : Width :=
  ⟨head.toNat / 64, by have := head.toNat_lt; omega⟩

/-- The value of a first byte and the bytes after it, for the width it selects. -/
def valueOf (head : UInt8) (tail : List UInt8) : Nat :=
  head.toNat % 64 * 256 ^ tailLength (selector head) + bytesToNat tail

/-- A first byte and as many tail bytes as it selects give a value below `2^62`. -/
theorem valueOf_lt (head : UInt8) (tail : List UInt8)
    (h : tail.length = tailLength (selector head)) : valueOf head tail < 2 ^ 62 := by
  have hbytes := bytesToNat_lt tail
  rw [h] at hbytes
  have hhead : head.toNat % 64 + 1 ≤ 64 := by omega
  have hv : valueOf head tail < capacity (selector head) := by
    unfold valueOf capacity
    calc
      _ < (head.toNat % 64 + 1) * 256 ^ tailLength (selector head) := by
        rw [Nat.succ_mul]
        omega
      _ ≤ _ := Nat.mul_le_mul_right _ hhead
  exact Nat.lt_of_lt_of_le hv (capacity_le _)

/-- Read one integer, returning the bytes after it and accepting longer representations.

RFC 9000 §16 gives the length in the high two bits of the first byte.

Only the bytes of the integer are measured, so reading many integers stays linear. -/
def decode : List UInt8 → Except VarintError (Varint × List UInt8)
  | [] => .error .truncated
  | head :: rest =>
    let count := tailLength (selector head)
    let tail := rest.take count
    if h : tail.length = count then
      .ok (⟨valueOf head tail, valueOf_lt head tail h⟩, rest.drop count)
    else .error .truncated

end Varint
end EthLib.Networking.Quic
