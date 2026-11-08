module

public import EthLib.Cryptography.Sphincs.Errors
public import EthLib.Cryptography.Sphincs.KeyGen

/-!
# leanSPHINCS signing

Signing.

Signing is stateless and deterministic: one key and one message give one signature.

The message digest picks the FORS instance, and each layer signs what the layer below it gives:

- The bottom key signs the FORS public key of instance `idx`.
- The middle key signs the root of bottom tree `idx >> 8`.
- The top key signs the root of middle tree `idx >> 16`.

The digest picks the instance at random, so instances get reused.

A FORS instance stays secure over a few signatures, and its security falls with each one.

So one key must sign at most `2^30` messages.

Source: `slh_sign_internal` of [FIPS 205][fips205] (Algorithm 19).

[fips205]: https://doi.org/10.6028/NIST.FIPS.205
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

variable {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))

/-- `M_l`: what the one-time key of a layer on the way from `idx` up signs.

- The bottom key signs the FORS public key of instance `idx`.
- A higher key signs the root of the tree below it, the tree its own index names. -/
def layerMessage (pkSeed : PkSeed) (prf : Prf m) (layer : Layer) (idx : Nat) : m Digest :=
  match layer with
  | .bottom => forsKey H pkSeed prf idx
  | .middle => treeRoot H pkSeed prf .bottom (OtsKey.ofIndex .bottom idx).tree
  | .top => treeRoot H pkSeed prf .middle (OtsKey.ofIndex .middle idx).tree

/-- One layer's signature of a message: the one-time signature and the path of the key.

The key is the layer's key on the way from `idx` up.

# Errors

- No counter gives a codeword, which happens with probability below `exp(-2^18)`. -/
def signLayer (pkSeed : PkSeed) (prf : Prf m) (layer : Layer) (idx : Nat) (msg : Digest) :
    m (Except SphincsError (LayerSignature layer)) := do
  let key := OtsKey.ofIndex layer idx
  -- No codeword is an error.
  let some (counter, chainValues) ← otsSign H pkSeed prf key msg
    | return .error (.noAdmissibleEncoding layer)
  -- A one-time signature is packed with the key's path.
  return .ok { counter, chainValues, path := ← path H pkSeed prf layer key.tree key.leaf }

/-- Sign a message from a source of secrets, the public key and the randomizer `R`.

1. `R` and the message give the digest: the index and one leaf per FORS tree.
2. FORS instance `idx` opens those leaves.
3. Each layer's key signs what the layer below gives, with its path.

# Errors

- A one-time signature finds no codeword. -/
def signDerived (prf : Prf m) (pk : PublicKey) (rho : Randomizer) (msg : Message) :
    m (Except SphincsError Signature) := do
  let pkSeed := pk.pkSeed
  -- Step 1: the digest of the message under `R`.
  let d ← hMsg H rho pkSeed pk.root msg
  let idx := digestIndex d
  -- Step 2: open the FORS instance at the digest's leaves.
  let fors ← forsSign H pkSeed prf idx (digestLeaves d)
  -- Step 3: sign up the hypertree, each layer what the layer below gives.
  let bottomMsg ← layerMessage H pkSeed prf .bottom idx
  -- A layer's error ends signing, before any later hash call.
  let bottom ← match ← signLayer H pkSeed prf .bottom idx bottomMsg with
    | .ok sig => pure sig
    | .error err => return .error err
  let middleMsg ← layerMessage H pkSeed prf .middle idx
  let middle ← match ← signLayer H pkSeed prf .middle idx middleMsg with
    | .ok sig => pure sig
    | .error err => return .error err
  let topMsg ← layerMessage H pkSeed prf .top idx
  let top ← match ← signLayer H pkSeed prf .top idx topMsg with
    | .ok sig => pure sig
    | .error err => return .error err
  return .ok { randomizer := rho, fors, bottom, middle, top }

/-- `Sign(SK, M)` over a hash `H`: sign a message, FIPS 205's `slh_sign_internal`.

1. `PK.seed` and `SK.prf` from `SK.seed`, and `PK.root` from the top tree.
2. The randomizer `R = PRF_msg(SK.prf, PK.seed, M')`, with `opt_rand = PK.seed`.
3. The signature from `PRF(PK.seed, SK.seed, ADRS)`, the public key and `R`.

# Warning

Never sign more than `2^30` messages with one secret key.

# Errors

- A one-time signature finds no codeword. -/
def signWith (sk : SecretKey) (msg : Message) : m (Except SphincsError Signature) := do
  -- Step 1: the expanded key, then the public key, which builds the top tree.
  let key ← expandKey H sk.seed
  let secrets := prf H key.pkSeed sk.seed
  let pk ← publicKeyOf H key.pkSeed secrets
  -- Step 2: the randomizer, deterministic.
  let rho ← prfMsg H key.skPrf key.pkSeed msg
  -- Step 3: the digest, FORS and the three layers.
  signDerived H secrets pk rho msg

/-- `Sign(SK, M)`: sign a message.

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
