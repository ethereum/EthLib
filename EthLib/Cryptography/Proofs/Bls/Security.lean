module

public import EthLib.Cryptography.Proofs.Bls.Security.PopEager
public import EthLib.Cryptography.Proofs.Bls.Security.PopExtract
public import EthLib.Cryptography.Proofs.Bls.Security.PopReduction
public import EthLib.Cryptography.Proofs.Bls.Security.Refinement

/-!
# Proofs: the security of BLS signatures

In the random oracle model, a BLS forger gives a solver of a co-Diffie-Hellman problem.

A forger within `q` hash calls wins at most `q` times as often as that solver.

EthLib's signing and verification compute the scheme of that game.

The byte game reduces a forger on compressed encodings to a group-element forger.

Freshness excludes every message submitted to signing, regardless of signature bytes.

A second game states unforgeability of aggregates with proofs of possession.

The algebraic step of its reduction is proved, on programmed hashes.

A valid aggregate with valid proofs on key hashes `r x • Z` gives `a • Z`, for the key `a • g1`.

That needs every key to be a multiple of `g1`, no `r x` to be zero, and a nonzero honest count.

The game is unchanged in distribution when one message hash scalar is drawn right after the key.

The reduction answers every oracle without the secret key.

When the scalar drawn first is nonzero, its run follows the game's until that message is signed.

No bound on the aggregate game is proved yet.
-/
