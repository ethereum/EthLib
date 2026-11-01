module

public import EthLib.Cryptography.Hash.Sha256

/-!
# `Exports.Sha256`

C-ABI export for the SHA-256 hash function, FIPS 180-4 §6.2, callable from the Python C extension.

The input is a `ByteArray` of any length, and the output is its 32-byte digest.

The function is total, so this export, unlike the BLS and KZG ones, has no `IO` error path.
-/

public section

namespace EthLib.Cryptography.Hash.Exports

/-- SHA-256 of the message, FIPS 180-4 §6.2.

Hashing is the step every protocol shares.

Clients call this export rather than re-rolling the padding and the compression on their side. -/
@[export eth_sha256]
def sha256 (data : ByteArray) : ByteArray :=
  EthLib.Cryptography.Hash.sha256 data

end EthLib.Cryptography.Hash.Exports
