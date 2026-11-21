module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the decoded Lagrange points 2048 to 3071 of the embedded setup

Each theorem checks in the kernel that 16 Lagrange strings encode their table entries.

Decompression of such a string gives its entry, so the kernel computes no square root.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

decode_checks decodeL tableL TrustedSetupData.g1LagrangeHex 128 192

end EthLib.Cryptography.Kzg.SetupLagrange
