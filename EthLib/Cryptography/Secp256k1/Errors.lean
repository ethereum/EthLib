module



/-!
# `Secp256k1.Errors`

Typed errors for secp256k1.

The specification does no I/O, so a fallible function returns `Except Secp256k1Error`.
-/

@[expose] public section

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
  /-- An integer `r` or `s` of a signature was not in `[1, n - 1]`. -/
  | scalarOutOfRange
  /-- A private key was zero, which is not in `[1, n - 1]`. -/
  | zeroPrivateKey
  /-- The point `R` of a signature had `x >= n`, which the recovery ids 0 and 1 cannot name. -/
  | unrecoverableNonce
  /-- The nonce generator gave no usable nonce within its bound on attempts. -/
  | noNonce
deriving DecidableEq, Repr

/-- A message for a rejection, phrased for someone reading a Python traceback. -/
def Secp256k1Error.message : Secp256k1Error → String
  | .invalidEncodingLength size => s!"bad point encoding size: {size}, expected 33 or 65"
  | .invalidPrefix byte => s!"bad point encoding prefix: {byte}"
  | .coordinateTooLarge => "point coordinate is not below p"
  | .notOnCurve => "point is not on the curve"
  | .noPointWithX => "no point of the curve has this x"
  | .pointAtInfinity => "the point at infinity is not a public key"
  | .scalarOutOfRange => "signature integer is not in [1, n - 1]"
  | .zeroPrivateKey => "private key is zero"
  | .unrecoverableNonce => "nonce point has x >= n, so no recovery id 0 or 1 names it"
  | .noNonce => "no usable nonce within the bound on attempts"

end EthLib.Cryptography.Secp256k1
