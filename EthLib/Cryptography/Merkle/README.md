# Merkle trees

A Merkle tree commits to many values with one short value, its root.

A short proof, the path, then shows that one value is among them.

This module defines perfect binary Merkle trees once, for every primitive that builds one.

## The tree

A tree of height `h` has `2^h` leaves.

Every node has a position `(level, j)`: level 0 holds the leaves, and level `h` holds the root.

The children of node `(level + 1, j)` are `(level, 2j)` and `(level, 2j + 1)`.

```text
    X_{level+1,j} = hash(level + 1, j, X_{level,2j}, X_{level,2j+1})
```

The node hash receives the position of the node it computes.

- A hash-based signature reads it, to hash every node under its own address.
- A plain tree ignores it, and hashes every node alike.

So one definition serves both kinds, and every theorem holds for both.

## Paths

The path of a leaf holds the sibling of each of its ancestors, from the leaf up.

Climbing from the leaf, each step hashes the node held with the next sibling.

The low bit of the index says whether the held node is the left or the right child.

The index is halved at each step, so it always names the node held.

## What is proved

The proofs are in `EthLib/Cryptography/Proofs/Merkle/`, for every node hash.

- Completeness.
  Climbing from a leaf with its path reaches its ancestor on the top level, the root for a leaf below `2^h` (`climb_path`, `climb_path_root`).
- Binding.
  Two climbs from one position that meet are equal, or the node hash collides (`climb_binding`).
  The collision is at an ancestor of the starting node, so a hash tweaked by its position collides under one tweak.
- Second preimages.
  A climb that reaches an honest node but is not the honest one gives a second preimage of an honest ancestor (`climb_binding_node`).
  One side of it is that ancestor's two honest children.
- Trees that ignore the position.
  Each node is the root of the subtree of leaves below it (`node_const_shift`).

## What is not proved

- Any bound on the cost of a collision or a second preimage.
  The theorems turn a forged opening into one.
  How hard that is depends on the hash.
