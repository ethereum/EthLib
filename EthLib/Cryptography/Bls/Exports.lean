import EthLib.Cryptography.Bls.Signatures
import EthLib.Cryptography.Bls.Errors

/-!
# `Bls.Exports`

C-ABI exports for the BLS spec functions, callable from the Python C
extension. Same conventions as the KZG exports: inputs are `ByteArray`
or `Array ByteArray`; booleans come back as `UInt8`.
-/

namespace EthLib.Cryptography.Bls.Exports

open EthLib.Cryptography.Bls.Signatures

@[export eth_bls_aggregate_pubkeys]
def ethAggregatePubkeysExport
    (pubkeys : @& Array ByteArray) : IO ByteArray :=
  runBls (ethAggregatePubkeys pubkeys)

@[export eth_bls_fast_aggregate_verify]
def ethFastAggregateVerifyExport
    (pubkeys : @& Array ByteArray) (msg : @& ByteArray) (sig : @& ByteArray)
    : IO UInt8 := do
  return if ethFastAggregateVerify pubkeys msg sig then 1 else 0

end EthLib.Cryptography.Bls.Exports
