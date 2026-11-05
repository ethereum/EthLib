module

public import EthLib.Cryptography.Sphincs.Digest

/-!
# leanSPHINCS verification

Signature verification.

1. Hash `m` and `R` into the digest `D`, and read `idx` and the 24 leaves from it.
2. Recover the FORS key `K = Fts.recover(idx, leaves, fors)`.
3. Bottom layer: `X_0 = Tree.fold(Ots.leaf(K, c_0, y_0), pi_0)`.
4. Middle layer: `X_1 = Tree.fold(Ots.leaf(X_0, c_1, y_1), pi_1)`.
5. Top layer: `X_2 = Tree.fold(Ots.leaf(X_1, c_2, y_2), pi_2)`.
6. Accept when no `Ots.leaf` fails and `X_2` is the public key's root.

Each one-time key and its tree are the ones on the way from `idx` up.

# Cost

A constant 492 permutations of Keccak-f[1600], whatever the message.

A `k`-byte input costs `floor(k / 136) + 1` permutations:

- Digest: 2, one for each 80-byte call.
- FORS: `24 * 10 = 240`, a leaf and 9 nodes per tree, one each.
- Encodings: 6 for the 804-byte input of the FORS key, then 1 per layer above.
- Chains: `3v - T = 64` per layer, one each.
- Leaves: 8 per layer, for the 1056-byte input of 64 chain ends.
- Paths: `8 + 8 + 10 = 26`, one per level.

That is `2 + 240 + 8 + 192 + 24 + 26 = 492`.

Nothing here needs to be constant time: every value it reads is public.

Source: `Concrete.verify` in FORS/Scheme.lean.
<https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/formal/sphincs/FORS/Scheme.lean>
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-! ## Keys and signatures -/

/-- What a verifier knows about a signer. -/
structure PublicKey where
  /-- The root of the top tree. -/
  root : Digest
  /-- The public parameter every hash of this key is made under. -/
  publicParam : PublicParam
  deriving DecidableEq

/-- One layer's signature: a one-time signature and the path of its key. -/
structure LayerSignature (layer : Layer) where
  /-- The counter under which the signed message encodes to a codeword. -/
  counter : UInt32
  /-- One value per chain, revealed at the position its digit names. -/
  chainValues : Vector Digest V
  /-- The key's path, from the leaf up. -/
  path : Vector Digest layer.height
  deriving DecidableEq

/-- A signature: the randomizer, the FORS opening, and one signature per layer. -/
structure Signature where
  /-- The randomizer hashed with the message into the digest. -/
  randomizer : Randomizer
  /-- One opening per FORS tree, at the leaf the digest picks. -/
  fors : Vector TreeOpening FORS_TREES
  /-- The bottom key's signature of the FORS key. -/
  bottom : LayerSignature .bottom
  /-- The middle key's signature of the bottom tree's root. -/
  middle : LayerSignature .middle
  /-- The top key's signature of the middle tree's root. -/
  top : LayerSignature .top
  deriving DecidableEq

/-! ## Verification -/

variable {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))

/-- The root one layer's signature leads to, from the message it signs.

The signing key is the layer's key on the way from `idx` up.

Returns nothing when the counter does not encode the message as a codeword. -/
def layerRoot (pp : PublicParam) (layer : Layer) (idx : Nat) (msg : ByteArray)
    (sig : LayerSignature layer) : m (Option Digest) := do
  let key := OtsKey.ofIndex layer idx
  -- Recover the key's leaf from the one-time signature.
  let some leaf ← otsLeaf H pp key msg sig.counter sig.chainValues | return none
  -- Climb the key's path to its tree's root.
  return some (← fold H pp layer key.tree key.leaf leaf sig.path)

/-- `Ver(pk, m, sigma)` over a hash `H`: whether a signature signs a message under a public key.

1. The digest names the index and the leaf of each FORS tree.
2. The openings lead to a FORS key.
3. Each layer, from the bottom up, signs what the layer below leads to.

A layer that fails ends verification, before any later hash call. -/
def verifyWith (pk : PublicKey) (msg : Message) (sig : Signature) : m Bool := do
  let pp := pk.publicParam
  -- Step 1: the digest names the index and the leaf of each FORS tree.
  let d ← messageDigest H pp msg sig.randomizer
  let idx := digestIndex d
  -- Step 2: the openings lead to a FORS key.
  let key ← forsRecover H pp idx (digestLeaves d) sig.fors
  -- Step 3: the bottom key signs the FORS key, and its path leads to a bottom root.
  let some bottomRoot ← layerRoot H pp .bottom idx (forsKeyBytes key) sig.bottom | return false
  -- Step 4: the middle key signs that root, and its path leads to a middle root.
  let some middleRoot ← layerRoot H pp .middle idx (packBytes bottomRoot) sig.middle
    | return false
  -- Step 5: the top key signs that root, and its path leads to the top root.
  let some root ← layerRoot H pp .top idx (packBytes middleRoot) sig.top | return false
  -- Step 6: no layer failed, and the top root is the key's.
  return decide (root = pk.root)

/-- `Ver(pk, m, sigma)`: whether a signature signs a message under a public key.

A yes or a no, never a reason.

Which step rejected a well-formed signature carries no meaning for the caller. -/
def verify (pk : PublicKey) (m : Message) (sig : Signature) : Bool :=
  (verifyWith hashId pk m sig).run

end EthLib.Cryptography.Sphincs
