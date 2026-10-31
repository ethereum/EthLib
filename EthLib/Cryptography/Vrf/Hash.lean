import EthLib.Cryptography.Hash.Keccak
import EthLib.Cryptography.Vrf.Types

/-!
# `Vrf.Hash`

The three hashes of the tree.

```text
    leaf(s) = keccak256(PQ_VRF_LEAF | s)
    node(l, r) = keccak256(PQ_VRF_NODE | l | r)
    output(s) = keccak256(PQ_VRF_OUTPUT | s)
```

Their inputs are 43, 75 and 45 bytes long, so no input of one is an input of another.

The output is not the leaf.

An opening reveals the leaf of its sibling index, and that must not reveal the sibling's output.
-/

namespace EthLib.Cryptography.Vrf

open EthLib.Cryptography.Vrf.Constants

/-- `keccak256`: Ethereum's hash, FIPS 202's 256-bit hash with Keccak's original padding. -/
def hash (input : ByteArray) : Digest :=
  Hash.Keccak.keccak256 input

/-- The bytes a leaf hash reads: the leaf prefix, then the secret. -/
def leafInput (secret : Digest) : ByteArray :=
  packBytes VRF_LEAF_DST ++ packBytes secret

/-- The bytes a node hash reads: the node prefix, then the left and the right child. -/
def nodeInput (left right : Digest) : ByteArray :=
  packBytes VRF_NODE_DST ++ packBytes left ++ packBytes right

/-- The bytes an output hash reads: the output prefix, then the secret. -/
def outputInput (secret : Digest) : ByteArray :=
  packBytes VRF_OUTPUT_DST ++ packBytes secret

/-- The leaf that commits to a secret. -/
def leafHash (secret : Digest) : Digest :=
  hash (leafInput secret)

/-- The parent of two nodes. -/
def nodeHash (left right : Digest) : Digest :=
  hash (nodeInput left right)

/-- The output of a secret. -/
def outputHash (secret : Digest) : Digest :=
  hash (outputInput secret)

end EthLib.Cryptography.Vrf
