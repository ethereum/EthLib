module

public import EthLib.Cryptography.Hash.Crc32c

/-!
# Exports: CRC-32C

The C export of CRC-32C, RFC 3720 §12.1, for the Python bindings.

CRC-32C is total, so the export has no error path.
-/

public section

namespace EthLib.Cryptography.Hash.Exports

/-- The four CRC-32C digest bytes of a message of any length, in the order of RFC 3720 §12.1. -/
@[export eth_crc32c]
def crc32c (data : ByteArray) : ByteArray :=
  ⟨(EthLib.Cryptography.Hash.Crc32c.digest data).toArray⟩

end EthLib.Cryptography.Hash.Exports
