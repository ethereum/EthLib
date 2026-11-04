module

public import EthLib.Cryptography.Proofs.Bls.Security.Reduction

/-!
# Proofs: the security of BLS signatures

In the random oracle model, a BLS forger gives a solver of a co-Diffie-Hellman problem.

A forger within `q` hash calls wins at most `q` times as often as that solver.
-/
