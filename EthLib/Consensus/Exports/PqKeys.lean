module

public import EthLib.Consensus.Exports.Ssz
public import EthLib.Consensus.PqKeys.Containers
public import EthLib.Consensus.PqKeys.Possession

/-!
# `Exports.PqKeys`

C-ABI exports of the post-quantum key registry.

No fork includes the registry yet, so the exports name no fork.

The first decodes the bytes of a container.

It returns the pair of the root and the bytes encoded again.

It takes and returns typed Python values.

The others compute the root that a proof of possession signs, and check a proof.

A name with no container or configuration, or an input of the wrong length, comes back as code 0.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz PqKeys
open EthLib.Exports (Result PyValue pyExport)
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

/-- The root of the value that the bytes encode, and the bytes of that value. -/
def pqKeysSszOf (args : String × ByteArray) : Result (Root × ByteArray) := do
  let (type, data) := args
  let some container := pqKeysContainerOf type
    | throw (0, s!"no container {type} in the post-quantum key registry")
  let value ← runSsz "input rejected" (SszType.deserialize container.type data)
  let root ← runSsz "root rejected" (SszType.hashTreeRoot value)
  let bytes ← runSsz "value rejected" (SszType.serialize value)
  return (root, bytes)

/-- The root of the value that the bytes encode, and the bytes of that value, as a pair.

The arguments are the name of the container and the bytes. -/
@[export eth_pq_keys_ssz]
def pqKeysSszExport (args : PyValue) : Result PyValue := pyExport pqKeysSszOf args

/-- The bytes of a fixed-size input, or code 0 when the length differs. -/
def exactBytes (n : Nat) (what : String) (bytes : ByteArray) : Result (Vector UInt8 n) :=
  if h : bytes.size = n then return ⟨bytes.data, h⟩
  else throw (0, s!"{what} must be {n} bytes, not {bytes.size}")

/-- The root that a proof of possession signs, for a configuration named in UTF-8. -/
@[export eth_pq_keys_possession_signing_root]
def possessionSigningRootExport (name genesisValidatorsRoot pubkey xmssPublicKey : ByteArray) :
    Result ByteArray := do
  let config ← configOf (← nameOf name)
  let genesisValidatorsRoot ← exactBytes 32 "genesis validators root" genesisValidatorsRoot
  let pubkey ← exactBytes 48 "pubkey" pubkey
  let xmssPublicKey ← exactBytes 32 "xmss public key" xmssPublicKey
  -- Every pair of keys has a root, so the error branch never runs.
  let .ok root := possessionSigningRoot config genesisValidatorsRoot pubkey xmssPublicKey
    | throw (0, "root rejected")
  return ⟨root.toArray⟩

/-- Whether a proof of possession is valid, as 1 or 0, for a configuration named in UTF-8. -/
@[export eth_pq_keys_is_valid_possession_proof]
def isValidPossessionProofExport
    (name genesisValidatorsRoot pubkey xmssPublicKey proof : ByteArray) : Result UInt8 := do
  let config ← configOf (← nameOf name)
  let genesisValidatorsRoot ← exactBytes 32 "genesis validators root" genesisValidatorsRoot
  let pubkey ← exactBytes 48 "pubkey" pubkey
  let xmssPublicKey ← exactBytes 32 "xmss public key" xmssPublicKey
  let proof ← exactBytes 2404 "proof" proof
  return if isValidPqPossessionProof config genesisValidatorsRoot pubkey xmssPublicKey proof then 1
    else 0

end EthLib.Consensus.Exports
