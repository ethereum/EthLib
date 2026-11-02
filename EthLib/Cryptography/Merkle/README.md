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

The tree never hashes on its own, so domain separation is the business of the primitive that passes the node hash.
Each primitive that uses the tree separates its node hash from every other hash it makes, and from the hashes of other protocols, as its own specification requires.
leanXMSS hashes a node with `Th`, under its public parameter and the node's address `A_node(l, lambda, j)`, which names the layer, the level and the index.
The VRF tree prefixes every node input with the 11 bytes `PQ_VRF_NODE`, and its proofs show that no node input is a leaf, secret or output input.
SSZ hashes the 64 bytes of the two children with SHA-256 and no prefix, because the SSZ specification fixes every root and a prefix would change them all.
A new primitive that builds on this module chooses its own separation in its node hash, and the theorems here hold whatever it chooses.

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
Completeness says that climbing from a leaf with its path reaches its ancestor on the top level, which is the root for a leaf below `2^h` (`climb_path`, `climb_path_root`, in `Completeness.lean`).
In a tree that ignores the position, each node is the root of the subtree of leaves below it (`node_const_shift`).

Binding needs more care, because a real node hash compresses two nodes into one and so has collisions.
A theorem that ended in "or a collision exists" would then hold for every hash and say nothing.
So the binding theorems in `Binding.lean` name an algorithm instead, which computes the collision from the forged opening, and prove that the algorithm succeeds.
`findCollision` walks two climbs from one position up, and returns the first level where they hash two different pairs to one parent.
`climb_binding` says that two climbs over equally many siblings that meet are equal, or `findCollision` returns a collision, and `findCollision_valid` says that every collision it returns is valid.
The collision is at an ancestor of the starting node, so a hash tweaked by its position collides under one tweak.
Against an honest tree the statement is sharper.
`findSecondPreimage` walks one climb against the honest tree, and returns the first level where it hashes a pair other than the honest children to an honest node (`climb_binding_node`, `findSecondPreimage_valid`).
Each search costs at most two hashes per level, plus the honest nodes it compares against, so whoever forges an opening also finds a collision or a second preimage at that cost.

No theorem bounds the probability of finding a collision or a second preimage.
The theorems turn a forged opening into one, and how hard that is depends on the hash.
