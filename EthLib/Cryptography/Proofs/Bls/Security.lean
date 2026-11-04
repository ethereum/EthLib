module

public import EthLib.Cryptography.Proofs.Bls.Security.Refinement

/-!
# Proofs: the security of BLS signatures

In the random oracle model, a BLS forger gives a solver of a co-Diffie-Hellman problem.

A forger within `q` hash calls wins at most `q` times as often as that solver.

Under the pairing law, EthLib's signing and verification compute the scheme of that game.

The game's adversary works on group elements, not on encoded bytes.
-/
