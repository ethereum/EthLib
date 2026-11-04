module

/-!
# `Secp256r1.Errors`

Typed errors for the bytes that secp256r1 verification reads.

The C exports pass the code and the message of an error to the bindings.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256r1

/-- Every way the bytes of a public key, a hash or a signature can be rejected. -/
inductive Secp256r1Error where
  /-- A public key was not 64 bytes long. -/
  | badPublicKeySize (size : Nat)
  /-- A coordinate of a public key was `p` or more. -/
  | coordinateTooLarge
  /-- A hash was not 32 bytes long. -/
  | badHashSize (size : Nat)
  /-- A signature was not 64 bytes long. -/
  | badSignatureSize (size : Nat)
deriving DecidableEq, Repr

/-- A message for a rejection, phrased for someone reading a Python traceback. -/
def Secp256r1Error.message : Secp256r1Error → String
  | .badPublicKeySize size => s!"bad public key size: {size}, expected 64"
  | .coordinateTooLarge => "bad public key: a coordinate is not below p"
  | .badHashSize size => s!"bad hash size: {size}, expected 32"
  | .badSignatureSize size => s!"bad signature size: {size}, expected 64"

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

A new constructor takes a new code, so that each code keeps its meaning. -/
def Secp256r1Error.code : Secp256r1Error → UInt32
  | .badPublicKeySize _ => 1
  | .coordinateTooLarge => 2
  | .badHashSize _ => 3
  | .badSignatureSize _ => 4

end EthLib.Cryptography.Secp256r1
