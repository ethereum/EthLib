module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Cryptography.Hash.Crc32

/-!
# Exports: CRC-32

The C exports of CRC-32, for the Python bindings.

CRC-32 is total, so only arguments that do not read as one `bytes` fail, with code 0.

Their argument and their result are typed Python values.
-/

public section

namespace EthLib.Cryptography.Hash.Exports

open EthLib.Exports (Result PyValue pyExport)

/-- The four CRC-32 digest bytes of a message of any length. -/
@[export eth_crc32]
def crc32 (args : PyValue) : Result PyValue :=
  pyExport (fun data => pure (EthLib.Cryptography.Hash.Crc32.digest data)) args

/-- CRC-32 as a number, the value of RFC 1952 §8, of a message of any length. -/
@[export eth_crc32_number]
def crc32Number (args : PyValue) : Result PyValue :=
  pyExport (fun data => pure (EthLib.Cryptography.Hash.Crc32.crc32 data)) args

end EthLib.Cryptography.Hash.Exports
