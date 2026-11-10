module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.ForwardCase
public import EthLib.Cryptography.Proofs.Secp256k1.Security.Game
public import EthLib.Cryptography.Proofs.Secp256k1.Security.InverseCase
public import EthLib.Cryptography.Proofs.Secp256k1.Security.JointGame
public import EthLib.Cryptography.Proofs.Secp256k1.Security.KeyOnly
public import EthLib.Cryptography.Proofs.Secp256k1.Security.KeyOnlyOutside
public import EthLib.Cryptography.Proofs.Secp256k1.Security.LazyGame
public import EthLib.Cryptography.Proofs.Secp256k1.Security.Origin
public import EthLib.Cryptography.Proofs.Secp256k1.Security.QueryBound
public import EthLib.Cryptography.Proofs.Secp256k1.Security.Redraw
public import EthLib.Cryptography.Proofs.Secp256k1.Security.Refinement

/-!
# Proofs: the security of ECDSA

The source is [Fersch, Kiltz, Poettering](https://doi.org/10.1145/2976749.2978413).

The game is existential unforgeability of ECDSA, in their bijective random oracle model, §4.

With the bijection the identity, EthLib's verification is the game's, for `r` and `s` below `n`.

A bound on the game applies to EthLib only if the identity behaves as a random bijection.

Every signature from EthLib's signing is the game's signature for some nonzero nonce.

With the bijection sampled lazily, every adversary wins with the same chance as in the game.

The game also runs over the joint state of its oracles.

The permutation oracle and the signer of new messages are parameters there.

Run the lazy game that way, then draw `Π` from the final cache of `Π`.

The forgery, the result, the signing cache and `Π` then have the joint law of the game.

Each pair of the cache of `Π` can also carry its origin: a forward or inverse query, or signing.

A forgery that wins has its pair in the final cache.

Its tag is `forward` if the final check asked first, and otherwise the tag it had before.

Take an adversary with at most `q_Π` queries to `Π` or its inverse.

Let it also make at most `q_S` signing queries.

The game as a program then asks `Π` or its inverse at most `q_Π + fuel · q_S + 1` times.

The key-only game gives the forger no signing oracle.

It is the chosen-message game of a forger that never asks for a signature.

Swap `Π` there for independent uniform answers.

Stop counting a win once a new answer repeats a cached value in the direction of its query.

The advantage falls by at most `q_Π (q_Π + 1) / 2` over `|A|`.

With independent answers, each new forward answer can be one query to an outside oracle.

The chance to win stays, and a replay fork can rewind the run at the forgery's query.

Both runs of the fork then queried the same point, with different answers.

With no flag raised, the check of a forgery read the logged answer at the fork index.

The map `ψ` sends that answer to `t`.

A new inverse answer that encodes a nonzero multiple of the base point can be redrawn.

The redraw knows its discrete logarithm.

The redrawn answer is still uniform.

A forgery whose point came from an inverse query then gives the discrete logarithm of the key.

Take a forger with at most `q` queries to `Π` or its inverse.

A win with no flag raised then has a fork index, or its point is not in the log of forward pairs.

No theorem bounds the advantage of a forger yet.
-/
