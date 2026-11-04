module

public import EthLib.Cryptography.Hash.Sha256

/-!
# Exports: SHA-256

The C export of SHA-256, FIPS 180-4 §6.2, for the Python bindings.

SHA-256 is total, so the export has no `IO` error path.
-/

public section

namespace EthLib.Cryptography.Hash.Exports

/--
The 32-byte SHA-256 digest of a message shorter than 2^61 bytes, FIPS 180-4 §6.2.

A longer message wraps its bit length modulo 2^64, and the result is not SHA-256.
-/
@[export eth_sha256]
def sha256 (data : ByteArray) : ByteArray :=
  EthLib.Cryptography.Hash.sha256 data

end EthLib.Cryptography.Hash.Exports
