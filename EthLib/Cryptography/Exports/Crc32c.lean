module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Cryptography.Hash.Crc32c

/-!
# Exports: CRC-32C

The C exports of CRC-32C, RFC 3720 §12.1, for the Python bindings.

CRC-32C is total, so only arguments that do not read as one `bytes` fail, with code 0.

Their argument and their result are typed Python values.
-/

public section

namespace EthLib.Cryptography.Hash.Exports

open EthLib.Exports (Result PyValue pyExport)

/-- The four CRC-32C digest bytes of a message of any length, in the order of RFC 3720 §12.1. -/
@[export eth_crc32c]
def crc32c (args : PyValue) : Result PyValue :=
  pyExport (fun data => pure (EthLib.Cryptography.Hash.Crc32c.digest data)) args

/-- CRC-32C as a number, the digest bytes read least significant byte first. -/
@[export eth_crc32c_number]
def crc32cNumber (args : PyValue) : Result PyValue :=
  pyExport (fun data => pure (EthLib.Cryptography.Hash.Crc32c.crc32c data)) args

end EthLib.Cryptography.Hash.Exports
