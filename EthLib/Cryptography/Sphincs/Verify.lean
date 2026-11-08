module

public import EthLib.Cryptography.Sphincs.Digest

/-!
# leanSPHINCS verification

Signature verification.

1. Hash `R` and `M` into the digest `H_msg(R, PK.seed, PK.root, M)`.
   Read `idx` and the 24 leaves `s` from it.
2. Recover the FORS public key `M_0 = Fors.recover(idx, s, openings)`.
3. For `l = 0, 1, 2`: `X_l = Wots.leaf(K_l(idx), M_l, c_l, sigma_l)`.
   Then `M_{l+1} = Tree.fold(K_l(idx), X_l, P_l)`.
4. Accept when no `Wots.leaf` fails and `M_3` is `PK.root`.

# Cost

A constant 515 permutations of Keccak-f[1600], whatever the message.

A `k`-byte input costs `floor(k / 136) + 1` permutations:

- Digest: 2, one for each 84-byte call of `H_msg`.
- FORS: `24 * (1 + 10) = 264`, a leaf of 64 bytes and 10 nodes of 80 bytes per tree.
- FORS public key: 4, for the 432-byte input of `T_k`.
- Encodings: 1 per layer, for the 68-byte input.
- Chains: `3v - T = 64` per layer, one each.
- Leaves: 8 per layer, for the 1072-byte input of `T_v`.
- Paths: `8 + 8 + 10 = 26`, one per height.

That is `2 + 264 + 4 + 3 + 192 + 24 + 26 = 515`.

Nothing here needs to be constant time: every value it reads is public.

Source: `slh_verify_internal` of [FIPS 205][fips205] (Algorithm 20).

[fips205]: https://doi.org/10.6028/NIST.FIPS.205
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-! ## Keys and signatures -/

/-- What a verifier knows about a signer: `PK = (PK.seed, PK.root)`. -/
structure PublicKey where
  /-- `PK.seed`, which every addressed hash of this key starts with. -/
  pkSeed : PkSeed
  /-- `PK.root`, the root of the top tree. -/
  root : Digest
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
  /-- The bottom key's signature of the FORS public key. -/
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
def layerRoot (pkSeed : PkSeed) (layer : Layer) (idx : Nat) (msg : Digest)
    (sig : LayerSignature layer) : m (Option Digest) := do
  let key := OtsKey.ofIndex layer idx
  -- Recover the key's leaf from the one-time signature.
  let some leaf ← otsLeaf H pkSeed key msg sig.counter sig.chainValues | return none
  -- Climb the key's path to its tree's root.
  return some (← fold H pkSeed layer key.tree key.leaf leaf sig.path)

/-- `Ver(PK, M, sigma)` over a hash `H`: whether a signature signs a message under a public key.

1. The digest names the index and the leaf of each FORS tree.
2. The openings lead to a FORS public key.
3. Each layer, from the bottom up, signs what the layer below leads to.

A layer that fails ends verification, before any later hash call. -/
def verifyWith (pk : PublicKey) (msg : Message) (sig : Signature) : m Bool := do
  -- Step 1: the digest names the index and the leaf of each FORS tree.
  let d ← hMsg H sig.randomizer pk.pkSeed pk.root msg
  let idx := digestIndex d
  -- Step 2: the openings lead to a FORS public key.
  let forsPk ← forsRecover H pk.pkSeed idx (digestLeaves d) sig.fors
  -- Step 3: the bottom key signs the FORS public key, and its path leads to a bottom root.
  let some bottomRoot ← layerRoot H pk.pkSeed .bottom idx forsPk sig.bottom | return false
  -- Step 4: the middle key signs that root, and its path leads to a middle root.
  let some middleRoot ← layerRoot H pk.pkSeed .middle idx bottomRoot sig.middle | return false
  -- Step 5: the top key signs that root, and its path leads to the top root.
  let some root ← layerRoot H pk.pkSeed .top idx middleRoot sig.top | return false
  -- Step 6: no layer failed, and the top root is the key's.
  return decide (root = pk.root)

/-- `Ver(PK, M, sigma)`: whether a signature signs a message under a public key.

A yes or a no, never a reason.

Which step rejected a well-formed signature carries no meaning for the caller. -/
def verify (pk : PublicKey) (m : Message) (sig : Signature) : Bool :=
  (verifyWith hashId pk m sig).run

end EthLib.Cryptography.Sphincs
