# Merkle trees

A Merkle tree commits to many values with one short value, its root.
A short proof, the path, then shows that one value is among them.
Hash-based signatures, SSZ and the VRF tree all build such trees, and this module defines them once, so that every primitive shares one definition and one set of proofs.

## The tree

A tree of height `h` has `2^h` leaves.
Every node has a position `(level, j)`: level 0 holds the leaves, level `h` holds the root, and `j` counts the nodes of a level from the left.
The children of node `(level + 1, j)` are `(level, 2j)` and `(level, 2j + 1)`, and the node is the hash of its two children:

```text
    X_{level+1,j} = hash(level + 1, j, X_{level,2j}, X_{level,2j+1})
```

The node hash receives the position of the node it computes.
A hash-based signature reads it, to hash every node under its own address.
SSZ and the VRF tree ignore it, and hash every node alike.
So one definition serves both kinds of tree, and every theorem holds for both.

Every definition runs in a monad, so that the hash may be an oracle that a security proof counts the calls to.
The order of the calls is fixed: a node computes its left subtree, then its right subtree, then its own hash, and a path and a climb go from the leaf up.
A pure tree runs in the identity monad.

## Paths

The path of a leaf holds the sibling of each of its ancestors, from the leaf up.
Climbing from the leaf, each step hashes the node held with the next sibling, and the low bit of the index says whether the held node is the left or the right child.
The index is halved at each step, so it always names the node held.

For example, take leaf 2 of a tree of height 2.
Its path is `X_{0,3}`, then `X_{1,0}`.

```text
step 1: held X_{0,2}, index 2 is even, so it is the left child:  X_{1,1} = hash(1, 1, X_{0,2}, X_{0,3})
step 2: held X_{1,1}, index 1 is odd, so it is the right child:  X_{2,0} = hash(2, 0, X_{1,0}, X_{1,1})
```

## What is proved

The proofs are in `EthLib/Cryptography/Proofs/Merkle/`, for every node hash.
Completeness says that climbing from a leaf with its path reaches its ancestor on the top level, which is the root for a leaf below `2^h` (`climb_path`, `climb_path_root`).
Binding says that two climbs from one position that meet are equal, or the node hash collides (`climb_binding`).
The collision is at an ancestor of the starting node, so a hash tweaked by its position collides under one tweak.
Against an honest tree the statement is sharper: a climb that reaches an honest node but is not the honest one gives a second preimage of an honest ancestor, whose other input is that ancestor's two honest children (`climb_binding_node`).
Finally, in a tree that ignores the position, each node is the root of the subtree of leaves below it (`node_const_shift`).

No theorem bounds the cost of a collision or a second preimage.
The theorems turn a forged opening into one, and how hard that is depends on the hash.
