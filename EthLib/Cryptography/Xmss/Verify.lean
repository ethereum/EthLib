module

public import EthLib.Cryptography.Xmss.Tree

/-!
# leanXMSS verification

Signature verification, the two layers one after the other.

Nothing here needs to be constant time: every value it reads is public.

Source: the leanXMSS specification draft, section "The scheme".

Each layer runs steps 2 to 7 of the verification of Construction 3 of [ePrint 2025/055][hbms], §4.2.

Construction 3 has one tree, where this scheme has two layers.

[hbms]: https://eprint.iacr.org/2025/055
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-! ## Keys and signatures -/

/-- What a verifier knows about a signer. -/
structure PublicKey where
  /-- `X^1_{16,0}`: the root of the top tree. -/
  root : Digest
  /-- The public parameter every hash of this key is made under. -/
  publicParam : PublicParam
  deriving DecidableEq

/-- One layer's signature: a one-time signature and the path of its key. -/
structure LayerSignature where
  /-- The randomizer under which the signed digest is a codeword. -/
  randomizer : Randomizer
  /-- One value per chain, revealed at the position its digit names. -/
  chainValues : Vector Digest V
  /-- The key's path, from the leaf up. -/
  path : Vector Digest LAYER_HEIGHT
  deriving DecidableEq

/-- A signature: its leaf index, and one signature per layer.

The top layer's signature is the same for every leaf index of one bottom tree. -/
structure Signature where
  /-- The leaf index the signature was made at. -/
  leafIndex : LeafIndex
  /-- The bottom key's signature of the message. -/
  bottom : LayerSignature
  /-- The top key's signature of the bottom tree's root. -/
  top : LayerSignature
  deriving DecidableEq

/-- The bottom tree a leaf index is in: `b = floor(idx / 2^16)`.

It is also the index of the top key that signs that tree's root. -/
def bottomTree (idx : LeafIndex) : Nat :=
  idx.toNat / 2 ^ LAYER_HEIGHT

/-! ## Verification -/

/-- The root one layer's signature leads to, from the message it signs.

Returns nothing when the signed digest is not a codeword. -/
def layerRoot {m : Type → Type} [Monad m] (H : Array UInt64 → m Lanes4)
    (publicParam : PublicParam) (layer : Layer) (e : Nat) (msg : Array UInt64)
    (sig : LayerSignature) : m (Option Digest) := do
  -- Recover the key's leaf, in 77 permutations, since `k` bytes cost `floor(k / 136) + 1`:
  -- - the digest, of 80 bytes on the bottom layer and 64 on the top, in 1;
  -- - the `3v - T = 68` chain steps, in 1 each;
  -- - the leaf, of the 960 bytes of 58 chain ends, in 8.
  --
  -- `e` is the signing key's index on its layer.
  --
  -- The message is 32 bytes on the bottom layer, and a 16-byte root on the top.
  let some leaf ← otsLeaf H publicParam layer (UInt32.ofNat e) msg sig.randomizer sig.chainValues
    | return none
  -- Climb the key's path to its tree's root, in 16 permutations, one per level.
  return some (← fold H publicParam layer e leaf sig.path)

/-- `Ver(pk, m, sigma)` over a hash `H`: whether a signature signs a message under a public key.

A yes or a no, never a reason.

Which step rejected a well-formed signature carries no consensus meaning.

It costs a fixed 186 permutations of Keccak-f[1600], so the aggregation circuit has a fixed size. -/
def verifyWith {m : Type → Type} [Monad m] (H : Array UInt64 → m Lanes4)
    (pk : PublicKey) (msg : Message) (sig : Signature) : m Bool := do
  let publicParam := pk.publicParam
  -- Step 1: `X = Tree.fold(0, idx, Ots.leaf(0, idx, m, rho^0, y^0), pi^0)`, in 93 permutations.
  -- The bottom key signs the message, so its path reaches bottom tree `b`'s root.
  let some bottomRoot ← layerRoot H publicParam .bottom sig.leafIndex.toNat msg.toArray sig.bottom
    | return false
  -- Step 2: `X' = Tree.fold(1, b, Ots.leaf(1, b, X, rho^1, y^1), pi^1)`, in 93 permutations.
  -- Here `b = floor(idx / 2^16)`.
  -- The top key `b` signs that root, so its path reaches the top root.
  let some root ← layerRoot H publicParam .top (bottomTree sig.leafIndex) bottomRoot.toArray sig.top
    | return false
  -- Step 3: accept exactly when neither `Ots.leaf` fails and `X' = root`.
  -- Only the top root is compared with the key's: the bottom root is the top layer's message.
  return decide (root = pk.root)

/-- `Ver(pk, m, sigma)`, with Keccak-256. -/
def verify (pk : PublicKey) (msg : Message) (sig : Signature) : Bool :=
  (verifyWith hashId pk msg sig).run

end EthLib.Cryptography.Xmss
