module

public import EthLib.Cryptography.Hash.Keccak

/-!
# Exports: Keccak-256

The C export of Keccak-256, for the Python bindings.

Keccak-256 is total, so the export has no `IO` error path.
-/

public section

namespace EthLib.Cryptography.Hash.Exports

/-- The 32-byte Keccak-256 digest of a message of any length, FIPS 202 with Keccak's padding. -/
@[export eth_keccak256]
def keccak256 (data : ByteArray) : ByteArray :=
  ⟨(EthLib.Cryptography.Hash.Keccak.keccak256 data).toArray⟩

end EthLib.Cryptography.Hash.Exports
