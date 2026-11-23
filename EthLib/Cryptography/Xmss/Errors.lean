module

public import EthLib.Cryptography.Xmss.Types

/-!
# leanXMSS errors

The ways a leanXMSS operation rejects its input.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-- Every way a leanXMSS operation can reject its input.

Bytes of the wrong length are an error.

A signature that parses but does not verify is not: verification returns `false`. -/
inductive XmssError where
  /-- A one-time key exhausted every randomizer without reaching a codeword. -/
  | noAdmissibleEncoding (layer : Layer) (key : Nat)
  /-- Public key bytes were not the public key length. -/
  | badPublicKeySize (actual : Nat)
  /-- Signature bytes were not the signature length. -/
  | badSignatureSize (actual : Nat)
  /-- Seed bytes were not the seed length. -/
  | badSeedSize (actual : Nat)
  /-- Message bytes were not the message length. -/
  | badMessageSize (actual : Nat)

/-- Human-readable description, used at the C-ABI boundary. -/
def XmssError.message : XmssError → String
  | .noAdmissibleEncoding layer key =>
      s!"no codeword within the trial limit for key {key} of layer {layer.toNat}"
  | .badPublicKeySize actual =>
      s!"bad public key size: {actual}, expected {PUB_KEY_SIZE}"
  | .badSignatureSize actual =>
      s!"bad signature size: {actual}, expected {SIG_SIZE}"
  | .badSeedSize actual =>
      s!"bad seed size: {actual}, expected {SEED_LEN}"
  | .badMessageSize actual =>
      s!"bad message size: {actual}, expected {MESSAGE_LEN}"

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

A new constructor takes a new code, so that each code keeps its meaning. -/
def XmssError.code : XmssError → UInt32
  | .noAdmissibleEncoding .. => 1
  | .badPublicKeySize _      => 2
  | .badSignatureSize _      => 3
  | .badSeedSize _           => 4
  | .badMessageSize _        => 5

end EthLib.Cryptography.Xmss
