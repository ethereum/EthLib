module

public import EthLib.Cryptography.Hash.Crc32

/-!
# Exports: CRC-32

The C export of CRC-32, for the Python bindings.

CRC-32 is total, so the export has no error path.
-/

public section

namespace EthLib.Cryptography.Hash.Exports

/-- The four CRC-32 digest bytes of a message of any length. -/
@[export eth_crc32]
def crc32 (data : ByteArray) : ByteArray :=
  ⟨(EthLib.Cryptography.Hash.Crc32.digest data).toArray⟩

end EthLib.Cryptography.Hash.Exports
