module

public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Check

/-!
# Proofs: monomial points 2304 to 2559 of the embedded setup

Each theorem checks 16 monomial points of `G1` in the kernel.

The check passes when each point has order dividing `r`.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupTorsion

torsion_checks g1Monomial_chunk TrustedSetupData.g1MonomialHex 144 160

end EthLib.Cryptography.Kzg.SetupTorsion
