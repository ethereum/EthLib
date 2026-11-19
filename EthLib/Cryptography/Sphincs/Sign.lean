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

/-- One layer's signature of a message: the one-time signature and the path of the key.

The key is the layer's key on the way from `idx` up, and its path is read from its built tree.

# Errors

- No counter gives a codeword, which happens with probability below `exp(-2^18)`. -/
def signLayer (pkSeed : PkSeed) (prf : Prf m) (layer : Layer) (idx : Nat)
    (tree : Merkle.Built Digest) (msg : Digest) :
    m (Except SphincsError (LayerSignature layer)) := do
  let key := OtsKey.ofIndex layer idx
  -- No codeword is an error.
  let some (counter, chainValues) ← otsSign H pkSeed prf key msg
    | return .error (.noAdmissibleEncoding layer)
  -- A one-time signature is packed with the key's path.
  return .ok { counter, chainValues, path := tree.path layer.height key.leaf }

/-- Sign a message from a source of secrets, `PK.seed`, the built top tree and the randomizer `R`.

The root of the top tree is `PK.root`.

1. `R` and the message give the digest: the index and one leaf per FORS tree.
2. FORS instance `idx` opens those leaves, and gives its public key.
3. Each layer's key signs what the layer below gives, with its path.

Each tree is built once, and gives both the path of a key and the root the layer above signs.

# Errors

- A one-time signature finds no codeword. -/
def signDerived (prf : Prf m) (pkSeed : PkSeed) (top : Merkle.Built Digest) (rho : Randomizer)
    (msg : Message) : m (Except SphincsError Signature) := do
  -- Step 1: the digest of the message under `R`.
  let d ← hMsg H rho pkSeed top.value msg
  let idx := digestIndex d
  -- Step 2: open the FORS instance at the digest's leaves.
  let (fors, forsPk) ← forsSign H pkSeed prf idx (digestLeaves d)
  -- Step 3: sign up the hypertree, each layer what the layer below gives.
  let bottomTree ← buildTree H pkSeed prf .bottom (OtsKey.ofIndex .bottom idx).tree
  -- A layer's error ends signing, before any later hash call.
  let bottom ← match ← signLayer H pkSeed prf .bottom idx bottomTree forsPk with
    | .ok sig => pure sig
    | .error err => return .error err
  let middleTree ← buildTree H pkSeed prf .middle (OtsKey.ofIndex .middle idx).tree
  let middle ← match ← signLayer H pkSeed prf .middle idx middleTree bottomTree.value with
    | .ok sig => pure sig
    | .error err => return .error err
  -- The top key's tree is the one top tree, already built.
  let top ← match ← signLayer H pkSeed prf .top idx top middleTree.value with
    | .ok sig => pure sig
    | .error err => return .error err
  return .ok { randomizer := rho, fors, bottom, middle, top }

/-- `Sign(SK, M)` over a hash `H`: sign a message, FIPS 205's `slh_sign_internal`.

1. `PK.seed` and `SK.prf` from `SK.seed`, then the top tree, whose root is `PK.root`.
2. The randomizer `R = PRF_msg(SK.prf, PK.seed, M')`, with `opt_rand = PK.seed`.
3. The signature from `PRF(PK.seed, SK.seed, ADRS)`, `PK.seed`, the top tree and `R`.

# Warning

Never sign more than `2^30` messages with one secret key.

# Errors

- A one-time signature finds no codeword. -/
def signWith (sk : SecretKey) (msg : Message) : m (Except SphincsError Signature) := do
  -- Step 1: the expanded key, then the top tree, built once for `PK.root` and the top path.
  let key ← expandKey H sk.seed
  let secrets := prf H key.pkSeed sk.seed
  let top ← buildTree H key.pkSeed secrets .top 0
  -- Step 2: the randomizer, deterministic.
  let rho ← prfMsg H key.skPrf key.pkSeed msg
  -- Step 3: the digest, FORS and the three layers.
  signDerived H secrets key.pkSeed top rho msg

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
