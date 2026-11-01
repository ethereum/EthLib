module

public import EthLib.Cryptography.Hash.Sha256

/-!
# `Exports.Sha256`

The C export of SHA-256, FIPS 180-4 §6.2, for the Python bindings.

SHA-256 is total, so the export has no `IO` error path.
-/

public section

namespace EthLib.Cryptography.Hash.Exports

/-- The 32-byte SHA-256 digest of a message of any length, FIPS 180-4 §6.2. -/
@[export eth_sha256]
def sha256 (data : ByteArray) : ByteArray :=
  EthLib.Cryptography.Hash.sha256 data

end EthLib.Cryptography.Hash.Exports
