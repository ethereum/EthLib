module

public import EthLib.Cryptography.Proofs.Bls.Security.MultiKey
public import EthLib.Cryptography.Proofs.Bls.Security.PopBound
public import EthLib.Cryptography.Proofs.Bls.Security.PopByteGame
public import EthLib.Cryptography.Proofs.Bls.Security.PopEager
public import EthLib.Cryptography.Proofs.Bls.Security.PopExtract
public import EthLib.Cryptography.Proofs.Bls.Security.PopReduction
public import EthLib.Cryptography.Proofs.Bls.Security.PopRefinement
public import EthLib.Cryptography.Proofs.Bls.Security.PopWins
public import EthLib.Cryptography.Proofs.Bls.Security.PopZeroKey
public import EthLib.Cryptography.Proofs.Bls.Security.Refinement

/-!
# Proofs: the security of BLS signatures

In the random oracle model, BLS forgeries reduce to a co-Diffie-Hellman problem.

That holds for one signature against one or `n` honest keys.

It holds for aggregates with proofs of possession too.

Each module states its game, its reduction and its assumptions.
-/
