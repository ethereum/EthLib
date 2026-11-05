module

public import EthLib.Consensus.Exports.Ssz
public import EthLib.Consensus.PqKeys.Containers

/-!
# `Exports.PqKeys`

A C-ABI export that reads the bytes of a container of the post-quantum key registry.

No fork includes the registry yet, so the export names no fork and no preset.

The export decodes the bytes, then returns the root of the value and its bytes encoded again.

A name with no container comes back as code 0, since no error type covers it.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz PqKeys
open EthLib.Exports (Result)
open Serialization.Ssz.Exports (runSsz)

/-- The container of the registry with a name, as the source names it. -/
def pqKeysContainerOf : String → Option Container
  | "PQKeyMaterial" => some ⟨PQKeyMaterial⟩
  | "PQKeyRegistration" => some ⟨PQKeyRegistration⟩
  | "PQKeyPossession" => some ⟨PQKeyPossession⟩
  | "SignedPQKeyRegistration" => some ⟨SignedPQKeyRegistration⟩
  | "ValidatorPQKeyMaterial" => some ⟨ValidatorPQKeyMaterial⟩
  | "ValidatorPQKeyChangeEpochs" => some ⟨ValidatorPQKeyChangeEpochs⟩
  | "BuilderPQKeyMaterial" => some ⟨BuilderPQKeyMaterial⟩
  | "BuilderPQKeyChangeEpochs" => some ⟨BuilderPQKeyChangeEpochs⟩
  | "PQKeyRegistrations" => some ⟨PQKeyRegistrations⟩
  | _ => none

/-- The root of the value that the bytes encode, then the bytes of that value.

The container is named in UTF-8. -/
@[export eth_pq_keys_ssz]
def pqKeysSszExport (type data : ByteArray) : Result ByteArray := do
  let type ← nameOf type
  let some container := pqKeysContainerOf type
    | throw (0, s!"no container {type} in the post-quantum key registry")
  let value ← runSsz "input rejected" (SszType.deserialize container.type data)
  let root ← runSsz "root rejected" (SszType.hashTreeRoot value)
  let bytes ← runSsz "value rejected" (SszType.serialize value)
  return ⟨root.toArray⟩ ++ bytes

end EthLib.Consensus.Exports
