import EthLib.Cryptography.Sphincs.Errors
import EthLib.Cryptography.Sphincs.KeyGen

/-!
# `Sphincs.Sign`

Signing.

Signing is stateless and deterministic: one key and one message give one signature.

The message digest picks the FORS instance, and each layer signs what the layer below it gives:

- The bottom key signs the FORS key of instance `idx`.
- The middle key signs the root of bottom tree `idx >> 8`.
- The top key signs the root of middle tree `idx >> 16`.

The digest picks the instance at random, so instances get reused.

A FORS instance stays secure over a few signatures, and its security falls with each one.

So one key must sign at most `2^30` messages.

Source: `Seeded.sign` in [FORS/Scheme.lean](https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/formal/sphincs/FORS/Scheme.lean).
-/

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-- What the one-time key of a layer on the way from `idx` up signs.

- The bottom key signs the FORS key of instance `idx`.
- A higher key signs the root of the tree below it, the tree its own index names. -/
def layerMessage (pp : PublicParam) (seed : Seed) (layer : Layer) (idx : Nat) : ByteArray :=
  match layer with
  | .bottom => forsKeyBytes (forsKey pp seed idx)
  | .middle => packBytes (treeRoot pp seed .bottom (OtsKey.ofIndex .bottom idx).tree)
  | .top => packBytes (treeRoot pp seed .middle (OtsKey.ofIndex .middle idx).tree)

/-- One layer's signature of a message: the one-time signature and the path of the key.

The key is the layer's key on the way from `idx` up.

# Errors

- No counter gives a codeword, which happens with probability below `exp(-2^18)`. -/
def signLayer (pp : PublicParam) (seed : Seed) (layer : Layer) (idx : Nat) (msg : ByteArray) :
    Except SphincsError (LayerSignature layer) :=
  let key := OtsKey.ofIndex layer idx
  -- No codeword is an error.
  -- A one-time signature is packed with the key's path.
  (otsSign pp seed key msg).elim (.error (.noAdmissibleEncoding layer)) fun ots =>
    .ok { counter := ots.1, chainValues := ots.2, path := path pp seed layer key.tree key.leaf }

/-- `Sign(sk, m)`: sign a message.

1. The randomizer and the message give the digest: the index and one leaf per FORS tree.
2. FORS instance `idx` opens those leaves.
3. Each layer's key signs what the layer below gives, with its path.

# Warning

Never sign more than `2^30` messages with one secret key.

# Errors

- A one-time signature finds no codeword. -/
def sign (sk : SecretKey) (m : Message) : Except SphincsError Signature := do
  let seed := sk.seed
  let pp := sk.publicParam
  -- Step 1: the randomizer, then the digest it gives the message.
  let rho := randomizer pp seed m
  let d := messageDigest pp m rho
  let idx := digestIndex d
  -- Step 2: open the FORS instance at the digest's leaves.
  let fors := forsSign pp seed idx (digestLeaves d)
  -- Step 3: sign up the hypertree, each layer what the layer below gives.
  let bottom ← signLayer pp seed .bottom idx (layerMessage pp seed .bottom idx)
  let middle ← signLayer pp seed .middle idx (layerMessage pp seed .middle idx)
  let top ← signLayer pp seed .top idx (layerMessage pp seed .top idx)
  return { randomizer := rho, fors, bottom, middle, top }

end EthLib.Cryptography.Sphincs
