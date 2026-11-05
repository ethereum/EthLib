module

public import EthLib.Cryptography.Sphincs.Errors
public import EthLib.Cryptography.Sphincs.KeyGen

/-!
# leanSPHINCS signing

Signing.

Signing is stateless and deterministic: one key and one message give one signature.

The message digest picks the FORS instance, and each layer signs what the layer below it gives:

- The bottom key signs the FORS key of instance `idx`.
- The middle key signs the root of bottom tree `idx >> 8`.
- The top key signs the root of middle tree `idx >> 16`.

The digest picks the instance at random, so instances get reused.

A FORS instance stays secure over a few signatures, and its security falls with each one.

So one key must sign at most `2^30` messages.

Source: `Seeded.sign` in FORS/Scheme.lean.
<https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/formal/sphincs/FORS/Scheme.lean>
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

variable {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))

/-- What the one-time key of a layer on the way from `idx` up signs.

- The bottom key signs the FORS key of instance `idx`.
- A higher key signs the root of the tree below it, the tree its own index names. -/
def layerMessage (pp : PublicParam) (seed : Seed) (layer : Layer) (idx : Nat) : m ByteArray :=
  match layer with
  | .bottom => return forsKeyBytes (← forsKey H pp seed idx)
  | .middle => return packBytes (← treeRoot H pp seed .bottom (OtsKey.ofIndex .bottom idx).tree)
  | .top => return packBytes (← treeRoot H pp seed .middle (OtsKey.ofIndex .middle idx).tree)

/-- One layer's signature of a message: the one-time signature and the path of the key.

The key is the layer's key on the way from `idx` up.

# Errors

- No counter gives a codeword, which happens with probability below `exp(-2^18)`. -/
def signLayer (pp : PublicParam) (seed : Seed) (layer : Layer) (idx : Nat) (msg : ByteArray) :
    m (Except SphincsError (LayerSignature layer)) := do
  let key := OtsKey.ofIndex layer idx
  -- No codeword is an error.
  let some (counter, chainValues) ← otsSign H pp seed key msg
    | return .error (.noAdmissibleEncoding layer)
  -- A one-time signature is packed with the key's path.
  return .ok { counter, chainValues, path := ← path H pp seed layer key.tree key.leaf }

/-- Sign a message from the scheme seed `S` and the parameter `P`.

1. The randomizer and the message give the digest: the index and one leaf per FORS tree.
2. FORS instance `idx` opens those leaves.
3. Each layer's key signs what the layer below gives, with its path.

# Errors

- A one-time signature finds no codeword. -/
def signDerived (s : Seed) (pp : PublicParam) (msg : Message) :
    m (Except SphincsError Signature) := do
  -- Step 1: the randomizer, then the digest it gives the message.
  let rho ← randomizer H pp s msg
  let d ← messageDigest H pp msg rho
  let idx := digestIndex d
  -- Step 2: open the FORS instance at the digest's leaves.
  let fors ← forsSign H pp s idx (digestLeaves d)
  -- Step 3: sign up the hypertree, each layer what the layer below gives.
  -- A layer's error ends signing, before any later hash call.
  let bottom ← match ← signLayer H pp s .bottom idx (← layerMessage H pp s .bottom idx) with
    | .ok sig => pure sig
    | .error err => return .error err
  let middle ← match ← signLayer H pp s .middle idx (← layerMessage H pp s .middle idx) with
    | .ok sig => pure sig
    | .error err => return .error err
  let top ← match ← signLayer H pp s .top idx (← layerMessage H pp s .top idx) with
    | .ok sig => pure sig
    | .error err => return .error err
  return .ok { randomizer := rho, fors, bottom, middle, top }

/-- `Sign(sk, m)` over a hash `H`: sign a message.

1. The scheme seed `S` and the public parameter `P`, from the secret key's seed.
2. The signature from `S` and `P`.

# Warning

Never sign more than `2^30` messages with one secret key.

# Errors

- A one-time signature finds no codeword. -/
def signWith (sk : SecretKey) (msg : Message) : m (Except SphincsError Signature) := do
  -- Every secret derives from the scheme seed, not from the key's seed itself.
  let s ← schemeSeed H sk.seed
  let pp ← publicParamOf H s
  signDerived H s pp msg

/-- `Sign(sk, m)`: sign a message.

1. The randomizer and the message give the digest: the index and one leaf per FORS tree.
2. FORS instance `idx` opens those leaves.
3. Each layer's key signs what the layer below gives, with its path.

# Warning

Never sign more than `2^30` messages with one secret key.

# Errors

- A one-time signature finds no codeword. -/
def sign (sk : SecretKey) (m : Message) : Except SphincsError Signature :=
  (signWith hashId sk m).run

end EthLib.Cryptography.Sphincs
