module

public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Cryptography.Vrf.Types

/-!
# VRF hashes

The three hashes of the tree, and the hash that mixes an output with public randomness.

- A leaf hashes `PQ_VRF_LEAF`, then the secret: 43 bytes.
- A node hashes `PQ_VRF_NODE`, then the left and the right child: 75 bytes.
- An output hashes `PQ_VRF_OUTPUT`, the index on 4 bytes little-endian, then the secret: 49 bytes.
- A mixed value hashes `PQ_VRF_MIX`, the output, then the randomness: 74 bytes.

Leaf, node and mixed inputs have lengths that differ from each other and from output inputs.

A secret input of key generation is also 49 bytes, but its prefix is `PQ_VRF_SECRET`.

The two 13-byte prefixes differ, so no input of one hash is an input of another.

The output is not the leaf.

An opening reveals the leaf of its sibling index, and that must not reveal the sibling's output.

The output reads the index, so one secret placed at two indices gives two unrelated outputs.

A holder may still choose its secrets, and so its outputs, before it publishes the root.

A selection must therefore compare a mixed value, with randomness revealed after the root.
-/

@[expose] public section

namespace EthLib.Cryptography.Vrf

open EthLib.Cryptography.Vrf.Constants

/-- Keccak-256: the 256-bit hash of FIPS 202, with Keccak's original padding. -/
def hash (input : ByteArray) : Digest :=
  Hash.Keccak.keccak256 input

/-- The bytes a leaf hash reads: the leaf prefix, then the secret. -/
def leafInput (secret : Digest) : ByteArray :=
  packBytes VRF_LEAF_DST ++ packBytes secret

/-- The bytes a node hash reads: the node prefix, then the left and the right child. -/
def nodeInput (left right : Digest) : ByteArray :=
  packBytes VRF_NODE_DST ++ packBytes left ++ packBytes right

/-- The bytes an output hash reads: the output prefix, the index, then the secret.

The index is `LE32(i)`, its four bytes least significant first. -/
def outputInput (i : UInt32) (secret : Digest) : ByteArray :=
  packBytes VRF_OUTPUT_DST ++ packBytes (uintToBytes 4 i.toNat) ++ packBytes secret

/-- The bytes a mixed value reads: the mix prefix, the output, then the randomness. -/
def mixInput (output randomness : Digest) : ByteArray :=
  packBytes VRF_MIX_DST ++ packBytes output ++ packBytes randomness

/-- The leaf that commits to a secret. -/
def leafHash (secret : Digest) : Digest :=
  hash (leafInput secret)

/-- The parent of two nodes. -/
def nodeHash (left right : Digest) : Digest :=
  hash (nodeInput left right)

/-- The node hash at a position of the tree, in the identity monad.

The VRF tree hashes every node alike, so the position is ignored. -/
def treeHash (_level _j : Nat) (left right : Digest) : Id Digest :=
  pure (nodeHash left right)

/-- The output at index `i` of a secret. -/
def outputHash (i : UInt32) (secret : Digest) : Digest :=
  hash (outputInput i secret)

/-- An output mixed with randomness: the value a selection compares with its threshold.

The randomness must become known only after the root is published.

Otherwise the holder can choose secrets whose mixed values pass. -/
def mixOutput (output randomness : Digest) : Digest :=
  hash (mixInput output randomness)

end EthLib.Cryptography.Vrf
