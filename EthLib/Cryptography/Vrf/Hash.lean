module

public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Cryptography.Merkle.Tree
public import EthLib.Cryptography.Vrf.Types

/-!
# VRF hashes

The three hashes of the tree, and the hash that mixes an output with public randomness.

No input of one hash is an input of another, since their lengths or their prefixes differ.
-/

@[expose] public section

namespace EthLib.Cryptography.Vrf

open EthLib.Cryptography.Vrf.Constants

/-- Keccak-256: the 256-bit hash of FIPS 202, with Keccak's original padding. -/
def hash (input : ByteArray) : Digest :=
  Hash.Keccak.keccak256 input

/-- The bytes a leaf hash reads: the leaf prefix, then the secret. -/
def leafInput (secret : Digest) : ByteArray :=
  -- `PQ_VRF_LEAF`, then the secret: 43 bytes.
  packBytes VRF_LEAF_DST ++ packBytes secret

/-- The bytes a node hash reads: the node prefix, then the left and the right child. -/
def nodeInput (left right : Digest) : ByteArray :=
  -- `PQ_VRF_NODE`, then the left and the right child: 75 bytes.
  packBytes VRF_NODE_DST ++ packBytes left ++ packBytes right

/-- The bytes an output hash reads: the output prefix, the index, then the secret.

The index is `LE32(i)`, its four bytes least significant first. -/
def outputInput (i : UInt32) (secret : Digest) : ByteArray :=
  -- `PQ_VRF_OUTPUT`, the index on 4 bytes little-endian, then the secret: 49 bytes.
  --
  -- Leaf, node and mixed inputs have lengths that differ from each other and from this one.
  --
  -- A secret input of key generation is also 49 bytes, but its prefix is `PQ_VRF_SECRET`.
  --
  -- The two 13-byte prefixes differ, so a secret input is never an output input.
  packBytes VRF_OUTPUT_DST ++ packBytes (Base.ByteOrder.toLE 4 i.toNat) ++ packBytes secret

/-- The bytes a mixed value reads: the mix prefix, the output, then the randomness. -/
def mixInput (output randomness : Digest) : ByteArray :=
  -- `PQ_VRF_MIX`, the output, then the randomness: 74 bytes.
  packBytes VRF_MIX_DST ++ packBytes output ++ packBytes randomness

/-- The leaf that commits to a secret. -/
def leafHash (secret : Digest) : Digest :=
  hash (leafInput secret)

/-- The parent of two nodes. -/
def nodeHash (left right : Digest) : Digest :=
  hash (nodeInput left right)

/-- The node hash at a position of the tree, with `H` in place of Keccak-256.

The VRF tree hashes every node alike, so the position is ignored. -/
def nodeWith {m : Type → Type} [Monad m] (H : ByteArray → m Digest) (_p : Merkle.Position)
    (left right : Digest) : m Digest :=
  H (nodeInput left right)

/-- The node hash at a position of the tree, with Keccak-256. -/
def treeHash (p : Merkle.Position) (left right : Digest) : Id Digest :=
  nodeWith (m := Id) (fun x => pure (hash x)) p left right

/-- The output at index `i` of a secret. -/
def outputHash (i : UInt32) (secret : Digest) : Digest :=
  -- The output is not the leaf.
  --
  -- An opening reveals the leaf of its sibling index.
  --
  -- That leaf must not reveal the sibling's output.
  --
  -- The output reads the index, so one secret at two indices gives two different outputs.
  --
  -- Otherwise their two output inputs are a Keccak-256 collision.
  hash (outputInput i secret)

/-- An output mixed with randomness: the value a selection compares with its threshold.

The randomness must become known only after the root is registered.

Otherwise the holder can choose secrets whose mixed values pass.

The holder must not be able to bias that randomness either. -/
def mixOutput (output randomness : Digest) : Digest :=
  -- A holder may still choose its secrets, and so its outputs, before it registers the root.
  --
  -- A selection must therefore compare a mixed value, with randomness revealed after the root.
  hash (mixInput output randomness)

end EthLib.Cryptography.Vrf
