/-!
# `Secp256k1.Errors`

Typed errors for secp256k1.

The specification does no I/O, so a fallible function returns `Except Secp256k1Error`.
-/

namespace EthLib.Cryptography.Secp256k1

/-- Every way secp256k1 can reject its input. -/
inductive Secp256k1Error where
  /-- An encoded point was not 33 or 65 bytes long. -/
  | invalidEncodingLength (size : Nat)
  /-- The first byte of an encoded point was not `02`, `03` or `04`, or did not match its length. -/
  | invalidPrefix (byte : UInt8)
  /-- A coordinate was `p` or more. -/
  | coordinateTooLarge
  /-- An uncompressed point did not satisfy `y^2 = x^3 + 7`. -/
  | notOnCurve
  /-- A compressed `x` had no `y` on the curve: `x^3 + 7` is not a square. -/
  | noPointWithX
  /-- The input was the point at infinity, which is not a public key. -/
  | pointAtInfinity
deriving DecidableEq, Repr

end EthLib.Cryptography.Secp256k1
