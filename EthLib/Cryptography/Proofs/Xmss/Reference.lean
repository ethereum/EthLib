module

public import EthLib.Cryptography.Xmss.Sign

/-!
# Proofs: the stateless signer of the note

In the note, the secret key is the seed `S_0` alone, and signing rebuilds every tree it reads.

That signer is written here as the note writes it, as a reference for the proofs.

A theorem proves that the specification's signer returns the same signatures, byte for byte.

Another proves that key generation gives the same public key.

The security proofs reason about the stateless signer, then carry their bounds over.

Nothing here is exported or run.

Source: the leanXMSS specification draft, section "The scheme".
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))

/-- The public key of the derivations from a seed: the top tree's root and the parameter `P`.

Computing the root builds all `2^16` one-time keys of the top tree. -/
def publicKeyOf (prf : SeedPrf m) : m PublicKey := do
  let pp ← publicParamOf prf
  let root ← node H pp prf .top LAYER_HEIGHT 0
  return { root, publicParam := pp }

/-- `Gen` of the stateless scheme over a hash `H`: the secret key and the public key.

The secret key of the stateless scheme is the seed itself. -/
def statelessKeyGenWith (seed : Seed) : m (Seed × PublicKey) := do
  let s ← schemeSeed H seed
  return (seed, ← publicKeyOf H (seedPrf H s))

/-- One layer's signature by key `e` of a message: the one-time signature and the path.

The path is computed from the seed.

# Errors

- No randomizer trial gives a codeword. -/
def signLayer (pp : PublicParam) (prf : SeedPrf m) (layer : Layer) (e : Nat)
    (msg : ByteArray) : m (Except XmssError LayerSignature) := do
  -- No codeword is an error.
  let some (randomizer, chainValues) ← otsSign H pp prf layer (UInt32.ofNat e) msg
    | return .error (.noAdmissibleEncoding layer e)
  -- A one-time signature is packed with the key's path.
  return .ok { randomizer, chainValues, path := ← path H pp prf layer e }

/-- Sign a message at a leaf index, from the derivations of a seed and the parameter `P`.

1. The bottom key `idx` signs the message.
2. One build of bottom tree `b = floor(idx / 2^16)` gives the key's path and the root `X^0_{16,b}`.
3. The top key `b` signs that root.

# Errors

- Either layer's one-time signature finds no codeword. -/
def signDerived (prf : SeedPrf m) (pp : PublicParam) (idx : LeafIndex) (msg : Message) :
    m (Except XmssError Signature) := do
  -- A layer's error ends signing, before any later hash call.
  let some (randomizer, chainValues) ←
      otsSign H pp prf .bottom (UInt32.ofNat idx.toNat) (packBytes msg)
    | return .error (.noAdmissibleEncoding .bottom idx.toNat)
  -- The bottom tree is built once: the key's path and the root both come from it.
  let tree ← build H pp prf .bottom LAYER_HEIGHT (bottomTree idx)
  let bottom : LayerSignature :=
    { randomizer, chainValues, path := tree.path LAYER_HEIGHT idx.toNat }
  let top ← match ← signLayer H pp prf .top (bottomTree idx) (packBytes tree.value) with
    | .ok sig => pure sig
    | .error err => return .error err
  return .ok { leafIndex := idx, bottom, top }

/-- `Sig(S_0, idx, m)` of the stateless scheme over a hash `H`.

1. The scheme seed `S` and the public parameter `P`, from the seed.
2. The signature from the derivations of `S` and from `P`.

# Errors

- Either layer's one-time signature finds no codeword. -/
def statelessSignWith (seed : Seed) (idx : LeafIndex) (msg : Message) :
    m (Except XmssError Signature) := do
  let s ← schemeSeed H seed
  let pp ← publicParamOf (seedPrf H s)
  signDerived H (seedPrf H s) pp idx msg

/-- `Sig(S_0, idx, m)` of the stateless scheme, with Keccak-256. -/
def statelessSign (seed : Seed) (idx : LeafIndex) (msg : Message) : Except XmssError Signature :=
  (statelessSignWith hashId seed idx msg).run

end EthLib.Cryptography.Xmss
