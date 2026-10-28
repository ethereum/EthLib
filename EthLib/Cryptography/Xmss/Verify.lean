import EthLib.Cryptography.Xmss.Tree

/-!
# `Xmss.Verify`

Signature verification.

```text
    X  = Tree.fold(0, idx, Ots.leaf(0, idx, m, rho^0, y^0), pi^0)
    X' = Tree.fold(1, b,   Ots.leaf(1, b,   X, rho^1, y^1), pi^1)
    accept  iff  neither Ots.leaf fails and X' = root
```

`b = floor(idx / 2^16)` is the bottom tree of leaf index `idx`.

# Cost

A constant 186 permutations of Keccak-f[1600], whatever the message.

Per layer, for a `k`-byte input costing `floor(k / 136) + 1` permutations:

- Digest: 1, for 80 bytes on the bottom layer and 64 on the top.
- Chains: `3v - T = 68`, one permutation each.
- Leaf: 8, for the 960 bytes of 58 chain ends.
- Path: 16, one per level.

That is 93 per layer.

A fixed count is what keeps the aggregation circuit a fixed size.

Nothing here needs to be constant time: every value it reads is public.

Source: the leanXMSS specification draft, section "The scheme".
-/

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

Returns nothing when the signed digest is not a codeword.

# Arguments

- `e`: the signing key's index on its layer.
- `msg`: the 32-byte message on the bottom layer, a 16-byte root on the top. -/
def layerRoot (pp : PublicParam) (layer : Layer) (e : Nat) (msg : ByteArray)
    (sig : LayerSignature) : Option Digest := do
  -- Recover the key's leaf from the one-time signature.
  let leaf ← otsLeaf pp layer (UInt32.ofNat e) msg sig.randomizer sig.chainValues
  -- Climb the key's path to its tree's root.
  return fold pp layer e leaf sig.path

/-- `Ver(pk, m, sigma)`: whether a signature signs a message under a public key.

A yes or a no, never a reason.

Which step rejected a well-formed signature carries no consensus meaning. -/
def verify (pk : PublicKey) (msg : Message) (sig : Signature) : Bool :=
  let pp := pk.publicParam
  let root? : Option Digest := do
    -- Step 1: the bottom key signs the message, so its path reaches bottom tree `b`'s root.
    let bottomRoot ← layerRoot pp .bottom sig.leafIndex.toNat (packBytes msg) sig.bottom
    -- Step 2: the top key `b` signs that root, so its path reaches the top root.
    layerRoot pp .top (bottomTree sig.leafIndex) (packBytes bottomRoot) sig.top
  -- Step 3: neither layer failed, and the top root is the key's.
  decide (root? = some pk.root)

end EthLib.Cryptography.Xmss
