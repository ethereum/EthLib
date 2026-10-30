import EthLib.Cryptography.Vrf.Hash
import EthLib.Cryptography.Vrf.Tree

/-!
# `Vrf.KeyGen`

The tree over the `2^32` leaf secrets, and the secrets from one 32-byte seed.

Leaf `j` is the leaf hash of secret `s_j`, and every node is a node hash.

```text
    s_i = keccak256(PQ_VRF_SECRET | seed | LE32(i))
```

The holder stores the seed, not the `2^32` secrets.

It recomputes a secret, or a subtree, when it opens an index.

Verification never sees the seed, so this derivation is not consensus-critical.

It is specified so that any implementation rebuilds the same tree from the same seed.

Keccak-256, keyed by the seed and separated by its prefix, acts as a pseudorandom function of the index.
-/

namespace EthLib.Cryptography.Vrf

open EthLib.Cryptography.Vrf.Constants

/-! ## The tree of the secrets -/

/-- The leaves over the secrets `s_j`: leaf `j` commits to secret `j`. -/
def leaves (secrets : UInt32 → Digest) (j : Nat) : Digest :=
  leafHash (secrets (UInt32.ofNat j))

/-- The root of the tree over the secrets. -/
def root (secrets : UInt32 → Digest) : Digest :=
  Tree.root nodeHash VRF_TREE_HEIGHT (leaves secrets)

/-- The opening at index `i`: its secret and its path. -/
def opening (secrets : UInt32 → Digest) (i : UInt32) : Opening where
  secret := secrets i
  path := Tree.path nodeHash VRF_TREE_HEIGHT (leaves secrets) i.toNat

/-! ## The secrets of a seed -/

/-- The bytes a secret hash reads: the secret prefix, the seed, then the index. -/
def secretInput (seed : Seed) (i : UInt32) : ByteArray :=
  packBytes VRF_SECRET_DST ++ packBytes seed ++ packBytes (indexBytes i)

/-- `s_i`: the secret of leaf `i`. -/
def secret (seed : Seed) (i : UInt32) : Digest :=
  hash (secretInput seed i)

/-- The root of the tree of a seed: what the holder publishes.

The seed must be 32 uniformly random bytes, kept secret. -/
def keyGen (seed : Seed) : Digest :=
  root (secret seed)

/-- The opening at index `i` of the tree of a seed. -/
def prove (seed : Seed) (i : UInt32) : Opening :=
  opening (secret seed) i

/-- The output at index `i` of the tree of a seed. -/
def evaluate (seed : Seed) (i : UInt32) : Digest :=
  outputHash (secret seed i)

end EthLib.Cryptography.Vrf
