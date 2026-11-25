module

public import EthLib.Base.ByteOrder

/-!
# The SEC 1 encoding of coordinates

A coordinate as 32 big-endian bytes, by SEC 1 v2 §2.3.5 and §2.3.6, and the uncompressed form.

Every curve whose modulus has 32 bytes uses it, such as secp256k1 and secp256r1.
-/

@[expose] public section

namespace EthLib.Cryptography.ShortWeierstrass

/-- A coordinate as 32 bytes, by SEC 1 v2 §2.3.5, for a modulus of 32 bytes. -/
def coordinateToBytes {p : Nat} (x : Fin p) : List UInt8 :=
  -- Step 1: for a 32-byte odd prime `q = p`, `M` is `a` as `mlen = 32` octets, by §2.3.7.
  (Base.ByteOrder.toBE 32 x.val).toList

/-- A coordinate is 32 bytes long. -/
theorem length_coordinateToBytes {p : Nat} (x : Fin p) : (coordinateToBytes x).length = 32 := by
  simp [coordinateToBytes]

/-- Bytes as a coordinate, by SEC 1 v2 §2.3.6, or `none` unless their integer is below `p`. -/
def coordinateOfBytes? {p : Nat} (bytes : List UInt8) : Option (Fin p) :=
  -- Step 1: `a` is the integer of `M`, by §2.3.8, and "invalid" unless `a` lies in `[0, p-1]`.
  if h : Base.ByteOrder.ofBE bytes < p then some ⟨_, h⟩ else none

/-- The uncompressed encoding `04 ‖ x ‖ y` of an affine point, by SEC 1 v2 §2.3.3. -/
def encodeUncompressed {p : Nat} (x y : Fin p) : List UInt8 :=
  -- Steps 3.1 to 3.3: `X` from `x_P`, `Y` from `y_P`, and `M = 04 || X || Y`.
  0x04 :: (coordinateToBytes x ++ coordinateToBytes y)

end EthLib.Cryptography.ShortWeierstrass
