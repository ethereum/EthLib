module

public import EthLib.Cryptography.Proofs.Merkle.Completeness
public import EthLib.Cryptography.Proofs.Merkle.Binding
public import EthLib.Cryptography.Proofs.Merkle.RandomOracle
public import EthLib.Cryptography.Proofs.Merkle.Perfect

/-!
# Proofs: Merkle trees

Proofs about Merkle trees: a path reaches the root, and a path binds its leaf.

The tree is also the perfect tree of the oracle framework, so results carry over.
-/
