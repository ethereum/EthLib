module

public import EthLib.Cryptography.Proofs.Bls.Security.PopExtract
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

No bound on that game is proved yet.
-/
