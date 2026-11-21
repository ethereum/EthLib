module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the decoded monomial points 1024 to 2047 of the embedded setup

Each theorem checks in the kernel that 16 monomial strings encode their table entries.

Decompression of such a string gives its entry, so the kernel computes no square root.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

decode_checks decodeM tableM TrustedSetupData.g1MonomialHex 64 128

end EthLib.Cryptography.Kzg.SetupLagrange
