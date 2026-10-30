# Merkle trees

A perfect binary Merkle tree of height `h`, written once and shared by every primitive that builds one.

The node hash receives the level and the index of the node it computes.

- A hash-based signature puts them into an address, so every node hashes under its own tweak.
- A plain tree, such as SSZ's, ignores them.

So one definition covers both, and every theorem about it holds for both.

## Source

The tree, the path and the fold follow [RFC 8391](https://www.rfc-editor.org/rfc/rfc8391):

- §4.1.6, `treeHash`: a node from the two below it.
- §4.1.9, `buildAuth`: the path, one sibling per level, from the leaf up.
- §4.1.10, `XMSS_rootFromSig`: the root a leaf and its path lead to.

## Users

- leanXMSS (`EthLib/Cryptography/Xmss/Tree.lean`): the node hash is `Th` under the address `A_node(l, lambda, j)`.
- SSZ (`EthLib/Serialization/Ssz/Merkle/Merkleize.lean`): `subtreeRoot` is the root, with SHA-256 of the two children at every node.

## What is proved

The proofs are in `EthLib/Cryptography/Proofs/Merkle/`, and hold for every node hash.

- Completeness.
  An honest path leads from leaf `e` to its ancestor on the top level, and to the root when `e < 2^h` (`fold_path`, `fold_path_root`, `Tree.lean`).
- Binding.
  Two openings of one leaf index that fold to the same root are equal, or the node hash collides (`fold_binding`, `Binding.lean`).
  The collision is at a known level `lambda` and index `floor(e / 2^lambda)`, so for a tweaked hash it is under one address.
- Second preimages.
  An opening that reaches an honest root is honest, or one level holds a second preimage of an honest node (`fold_eq_node_binding`, `fold_eq_root_binding`).
  One input of the collision is that node's two honest children.
- Injectivity.
  A node hash injective at every position makes the fold injective in the leaf and the path (`fold_injective`).
- Trees whose node hash ignores the position.
  Each node is the root of the subtree below it, at any height (`node_const_shift`).

## What is not proved

- Any bound on the probability of a collision or a second preimage.
  The binding theorems turn a forged opening into a collision; how hard that is depends on the hash.
