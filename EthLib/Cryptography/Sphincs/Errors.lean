import EthLib.Cryptography.Sphincs.Types

/-!
# `Sphincs.Errors`

Typed failures for the leanSPHINCS surface.

Verification is not here.

Bytes that do not parse are a caller error and fail here.

A well-formed signature that does not verify is an ordinary `false`.
-/

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-- Every way a leanSPHINCS operation can reject its input. -/
inductive SphincsError where
  /-- A one-time key exhausted every counter without reaching a codeword. -/
  | noAdmissibleEncoding (layer : Layer)
  /-- Public key bytes were not the public key length. -/
  | badPublicKeySize (actual : Nat)
  /-- Signature bytes were not the signature length. -/
  | badSignatureSize (actual : Nat)
  /-- Seed bytes were not the seed length. -/
  | badSeedSize (actual : Nat)
  /-- Message bytes were not the message length. -/
  | badMessageSize (actual : Nat)

/-- Human-readable description, used at the C-ABI boundary. -/
def SphincsError.message : SphincsError → String
  -- One line per rejection, phrased for someone reading a Python traceback.
  | .noAdmissibleEncoding layer =>
      s!"no codeword within the counter limit on layer {layer.toNat}"
  -- The expected length is fixed by the parameter set.
  -- So it is read from there rather than carried in the error.
  | .badPublicKeySize actual =>
      s!"bad public key size: {actual}, expected {PUB_KEY_SIZE}"
  | .badSignatureSize actual =>
      s!"bad signature size: {actual}, expected {SIG_SIZE}"
  | .badSeedSize actual =>
      s!"bad seed size: {actual}, expected {SEED_LEN}"
  | .badMessageSize actual =>
      s!"bad message size: {actual}, expected {MESSAGE_LEN}"

end EthLib.Cryptography.Sphincs
