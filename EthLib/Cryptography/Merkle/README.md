# Merkle trees

A Merkle tree commits to many values with one short value, its root.
A short proof, the path, then shows that one value is among them.
Hash-based signatures, SSZ and the VRF tree all build such trees.
This module defines the tree once, so that every primitive shares one definition and one set of proofs.

## The tree

A tree of height `h` has `2^h` leaves.
Every node has a position `(level, j)`.
Level 0 holds the leaves, level `h` holds the root, and `j` counts the nodes of a level from the left.
The children of node `(level + 1, j)` are `(level, 2j)` and `(level, 2j + 1)`, and the node is the hash of its two children:

```text
    X_{level+1,j} = hash(level + 1, j, X_{level,2j}, X_{level,2j+1})
```

The node hash receives the position of the node it computes.
A hash-based signature reads it, to hash every node under its own address.
SSZ and the VRF tree ignore it, and hash every node alike.
So one definition serves both kinds of tree, and the completeness and binding theorems hold for both.

The tree never hashes on its own.
The primitive that passes the node hash also chooses its domain separation.

leanXMSS hashes a node with `Th`, under its public parameter and the address `A_node(l, lambda, j)`.
That address names the layer, the level and the index of the node.
The hypertree and the FORS trees of leanSPHINCS do the same, with addresses that also name the tree.

The VRF tree prefixes every node input with the 11 bytes `PQ_VRF_NODE`.
Its proofs show that no node input is also a leaf, secret or output input.
SSZ hashes the 64 bytes of the two children with SHA-256 and no prefix, as the SSZ specification fixes every root.
A new primitive chooses its own separation in its node hash.
The completeness and binding theorems hold whatever it chooses.

Every definition runs in a monad, so that the hash may be an oracle whose calls a security proof counts.
The order of the calls is fixed.
A node computes its left subtree, then its right subtree, then its own hash.
A path and a climb both go from the leaf up.
A pure tree runs in the identity monad.

## Paths

The path of a leaf holds the sibling of each of its ancestors, from the leaf up.
A climb starts from the leaf and hashes the node it holds with the next sibling, one level at a time.
The low bit of the index says whether the held node is the left or the right child.
The index is halved at each step, so it always names the node held.

For example, take leaf 2 of a tree of height 2.
Its path is `X_{0,3}`, then `X_{1,0}`.
In the first step, the climb holds `X_{0,2}`.
Index 2 is even, so the held node is the left child, and the climb computes `X_{1,1} = hash(1, 1, X_{0,2}, X_{0,3})`.
In the second step, it holds `X_{1,1}`.
Index 1 is odd, so the held node is the right child, and the climb computes the root `X_{2,0} = hash(2, 0, X_{1,0}, X_{1,1})`.

## What is proved

The proofs are in `EthLib/Cryptography/Proofs/Merkle/`.
The completeness and binding theorems hold for every node hash.
Completeness says that a climb from a leaf with its path reaches the leaf's ancestor on the top level (`climb_path`).
For a leaf below `2^h`, that ancestor is the root (`climb_path_root`).
In a tree that ignores the position, each node is the root of the subtree of leaves below it (`node_const_shift`).
A tree hashes only at the levels it spans, so two node hashes that agree on those levels build the same tree (`node_congr`, `climb_congr`).

Binding needs more care.
A real node hash compresses two nodes into one, so it has collisions.
A theorem that ended in "or a collision exists" would then hold for every hash and say nothing.
So the theorems in `Binding.lean` name an algorithm that computes the collision from the forged opening, and prove that it succeeds.

`findCollision` walks two climbs from one position up.
It returns the first level where they hash two different pairs to one parent.
`climb_binding` says that two climbs over equally many siblings that meet are equal, or `findCollision` returns a collision.
`findCollision_valid` says that every collision it returns is valid, and that its pairs are the ones the two climbs hash there.
The collision sits at an ancestor of the starting node, so a hash tweaked by its position collides under one tweak.

`climbPairs` lists the pairs a climb hashes, one per level.
`findCollision_mem_climbPairs` follows from `findCollision_valid`: each pair of the collision is an entry of its own climb's list.
So the collision lies among the hash inputs of the two climbs.

Against an honest tree, the statement is sharper.
`findSecondPreimage` walks one climb against the honest tree.
It returns the first level where the climb hashes a pair other than the honest children to an honest node.
`climb_binding_node` and `findSecondPreimage_valid` state this.
On the honest climb the search returns nothing (`findSecondPreimage_honest`), so the second case of `climb_binding_node` is not true for every climb.

Both searches take one step per level of the climb, and each step hashes the pairs it compares.
`findSecondPreimage` also computes the two honest children and the honest node that it compares against on each level.
Like the tree, both searches run in any monad.
The binding theorems run them in the identity monad, and `RandomOracle.lean` runs the same definitions against an oracle.

`RandomOracle.lean` proves query budgets and probability bounds for both searches when an oracle answers their hash calls.
The oracle assigns independent uniform answers to distinct `(level, position, left, right)` tuples and remembers repeated inputs.
The bounds exclude position-ignoring hashes, including those of SSZ and the VRF tree.
They make no security claim about a concrete hash or quantum queries.

With an empty initial cache and `N` possible answers, `prEvent_collision_le` bounds the probability of a collision among queried inputs by `q^2 / N` for at most `q` classical hash calls.
This bound exceeds the standard birthday bound `q(q - 1) / (2N)` by the factor `2q / (q - 1)`: at most 4 for `q >= 2`, and close to 2 for large `q`.
`prEvent_secondPreimage_le` bounds by `q / N` the probability that a queried input other than one fixed honest input has a target digest fixed before the run.
As a second-preimage bound, it takes the target to be the honest digest and the other answers to stay uniform given that digest.
That conditioning is a modelling step: the theorem does not tie the target to the honest input.

`findCollision_queryBound` gives at most `2h` calls, where `h` is the shorter path length.
For paths and leaves fixed before the oracle is sampled, `prEvent_findCollision_queryNode_le` bounds the success probability of the search by `(2h)^2 / N`.
For fixed honest leaves, `findSecondPreimage_queryBound` counts all calls, including repeated honest-node computations:

```text
Q(l, 0) = 0
Q(l, n+1) = 1 + 2*(2^l - 1) + (2^(l+1) - 1) + Q(l+1, n)
```

For a path of length `n` from level `l`, fixed with the leaves before the oracle is sampled, `prEvent_findSecondPreimage_queryNode_le` bounds the success probability by `Q(l, n)^2 / N`.
The budget `Q(l, n)` equals `2^(l+n+2) - 2^(l+2) - 2n`, because the search recomputes the honest nodes on every level.
The search queries at most `2^(l+n) - 1 + n` distinct inputs.
The budget is between one and four times that count: under two for a path of length 1, and near four only for long paths.
Its honest ancestors depend on oracle answers, so this search uses the birthday bound rather than the bound for one fixed target.
A search whose paths depend on oracle answers goes through the covered-event theorems `prEvent_findCollision_le` and `prEvent_findSecondPreimage_le`.
