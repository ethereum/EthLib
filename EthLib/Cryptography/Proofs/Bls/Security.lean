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

A second game states unforgeability of aggregates with proofs of possession; no bound is proved yet.

The algebraic step of its reduction is proved.

A forged aggregate gives the honest secret times the message hash.
-/
