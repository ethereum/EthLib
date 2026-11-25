module

public import EthLib.Cryptography.ShortWeierstrass.Encoding
public import EthLib.Base.Proofs.ByteOrder

/-!
# Proofs: the SEC 1 encoding of coordinates

The 32 bytes of a coordinate read back as that coordinate.

32 bytes that read as a coordinate are its bytes.
-/

@[expose] public section

namespace EthLib.Cryptography.ShortWeierstrass

open Base

variable {p : Nat}

/-- The 32 bytes of a coordinate hold its value, for a modulus of at most `2^256`. -/
theorem ofBE_coordinateToBytes (hp : p ≤ 2 ^ 256) (x : Fin p) :
    ByteOrder.ofBE (coordinateToBytes x) = x.val :=
  ByteOrder.ofBE_toBE_of_lt (Nat.lt_of_lt_of_le x.isLt (by simpa using hp))

/-- The 32 bytes of a coordinate read back as that coordinate. -/
theorem coordinateOfBytes?_coordinateToBytes (hp : p ≤ 2 ^ 256) (x : Fin p) :
    coordinateOfBytes? (coordinateToBytes x) = some x := by
  simp only [coordinateOfBytes?, ofBE_coordinateToBytes hp, x.isLt, dite_true]

/-- 32 bytes that read as a coordinate are the bytes of that coordinate. -/
theorem coordinateToBytes_of_coordinateOfBytes? {l : List UInt8} {x : Fin p} (hl : l.length = 32)
    (h : coordinateOfBytes? l = some x) : coordinateToBytes x = l := by
  simp only [coordinateOfBytes?] at h
  split at h
  · cases h
    exact ByteOrder.toList_toBE_ofBE_of_length hl
  · cases h

end EthLib.Cryptography.ShortWeierstrass
