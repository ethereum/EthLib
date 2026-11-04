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
  /-- A hash was not 32 bytes long. -/
  | badHashSize (size : Nat)
  /-- A signature was not 64 bytes long. -/
  | badSignatureSize (size : Nat)
  /-- A recovery id was neither 0 nor 1. -/
  | badRecoveryId (id : UInt8)
  /-- A private key was not 32 bytes long. -/
  | badPrivateKeySize (size : Nat)
  /-- A private key was `n` or more. -/
  | privateKeyTooLarge
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
  | .badHashSize size => s!"bad hash size: {size}, expected 32"
  | .badSignatureSize size => s!"bad signature size: {size}, expected 64"
  | .badRecoveryId id => s!"bad recovery id: {id}, expected 0 or 1"
  | .badPrivateKeySize size => s!"bad private key size: {size}, expected 32"
  | .privateKeyTooLarge => "bad private key: not below the group order n"

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

A new constructor takes a new code, so that each code keeps its meaning. -/
def Secp256k1Error.code : Secp256k1Error → UInt32
  | .invalidEncodingLength _ => 1
  | .invalidPrefix _ => 2
  | .coordinateTooLarge => 3
  | .notOnCurve => 4
  | .noPointWithX => 5
  | .pointAtInfinity => 6
  | .scalarOutOfRange => 7
  | .zeroPrivateKey => 8
  | .unrecoverableNonce => 9
  | .noNonce => 10
  | .badHashSize _ => 11
  | .badSignatureSize _ => 12
  | .badRecoveryId _ => 13
  | .badPrivateKeySize _ => 14
  | .privateKeyTooLarge => 15

end EthLib.Cryptography.Secp256k1
