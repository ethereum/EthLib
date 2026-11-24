module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.ChosenMessageBound
public import EthLib.Cryptography.Proofs.Secp256k1.Security.Collision
public import EthLib.Cryptography.Proofs.Secp256k1.Security.Conflict
public import EthLib.Cryptography.Proofs.Secp256k1.Security.DivisionResistance
public import EthLib.Cryptography.Proofs.Secp256k1.Security.ForwardCase
public import EthLib.Cryptography.Proofs.Secp256k1.Security.ForwardSolver
public import EthLib.Cryptography.Proofs.Secp256k1.Security.Game
public import EthLib.Cryptography.Proofs.Secp256k1.Security.InverseCase
public import EthLib.Cryptography.Proofs.Secp256k1.Security.JointGame
public import EthLib.Cryptography.Proofs.Secp256k1.Security.KeyOnly
public import EthLib.Cryptography.Proofs.Secp256k1.Security.KeyOnlyBound
public import EthLib.Cryptography.Proofs.Secp256k1.Security.KeyOnlyOutside
public import EthLib.Cryptography.Proofs.Secp256k1.Security.Keyless
public import EthLib.Cryptography.Proofs.Secp256k1.Security.KeylessForger
public import EthLib.Cryptography.Proofs.Secp256k1.Security.LazyGame
public import EthLib.Cryptography.Proofs.Secp256k1.Security.Origin
public import EthLib.Cryptography.Proofs.Secp256k1.Security.Programmed
public import EthLib.Cryptography.Proofs.Secp256k1.Security.QueryBound
public import EthLib.Cryptography.Proofs.Secp256k1.Security.Redraw
public import EthLib.Cryptography.Proofs.Secp256k1.Security.Refinement

/-!
# Proofs: the security of ECDSA

Bounds on a key-only forger and on a chosen-message forger of ECDSA.

The game is existential unforgeability, in the bijective random oracle model of the source.

The chosen-message bound has one more term than Theorem 1 of the source.

That term is the advantage of a solver of the discrete logarithm.

Source: [Fersch, Kiltz, Poettering, CCS 2016][fkp], §4, Theorems 1 and 2.

[fkp]: https://doi.org/10.1145/2976749.2978413
-/
