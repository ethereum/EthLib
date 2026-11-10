module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.Game
public import EthLib.Cryptography.Proofs.Secp256k1.Security.LazyGame
public import EthLib.Cryptography.Proofs.Secp256k1.Security.Refinement

/-!
# Proofs: the security of ECDSA

The source is [Fersch, Kiltz, Poettering](https://doi.org/10.1145/2976749.2978413).

The game is existential unforgeability of ECDSA, in their bijective random oracle model, §4.

With the bijection the identity, EthLib's verification is the game's, for `r` and `s` below `n`.

A bound on the game applies to EthLib only if the identity behaves as a random bijection.

Every signature from EthLib's signing is the game's signature for some nonzero nonce.

With the bijection sampled lazily, every adversary wins with the same chance as in the game.

No theorem bounds the advantage of a forger yet.
-/
