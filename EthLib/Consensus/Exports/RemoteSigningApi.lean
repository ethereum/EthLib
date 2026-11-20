module

public import EthLib.Consensus.RemoteSigningApi.Endpoints
public import EthLib.Consensus.RemoteSigningApi.Response
public import EthLib.Consensus.Exports.SlashingProtection
public import EthLib.Consensus.Exports.Parameters

/-!
# `Exports.RemoteSigningApi`

C-ABI exports of the Remote-signing API: the requests that a remote signer reads, and their roots.

A request comes as a JSON document, and one export writes it again as the signer reads it.

Another gives the root that the signer signs for it.

Two more run the endpoints of a signer: the list of its keys, and the signing of a request.

A secret key is 32 bytes, big-endian, and the record of slashing protection is EIP-3076 JSON text.

An unknown preset or configuration has code 0.

A document that is not a request has the code of its error.
-/

public section

namespace EthLib.Consensus.Exports

open Lean Base RemoteSigningApi
open EthLib.Exports (Result PyValue pyExport)

/-- The code and the message of a document that is not a request, on one line. -/
def requestFault (error : RequestError) : UInt32 × String :=
  (error.code, s!"request rejected: {(repr error).pretty 1000}")

/-- A request of the Remote-signing API, read and written again. -/
def readSigningRequestOf (args : String × PyValue) : Result PyValue := do
  let (name, document) := args
  let preset ← presetOf name
  let request ← (SigningRequest.ofJson preset document.toJson).mapError requestFault
  let written ← (request.toJson).mapError fun fault => (0, s!"request not written: {reprStr fault}")
  return PyValue.ofJson written

/-- A request of the Remote-signing API, read and written again as the signer reads it.

The arguments are the name of the preset and the JSON document of the request.

The result holds every field that the request reads, and no other field.

An unknown preset has code 0.

A document that is not a request has the code of its error. -/
@[export eth_consensus_read_signing_request]
def readSigningRequestExport (args : PyValue) : Result PyValue :=
  pyExport readSigningRequestOf args

/-- The root that a remote signer signs for a request of the Remote-signing API. -/
def signingRequestRootOf (args : String × String × PyValue) : Result ByteArray := do
  let (name, configName, document) := args
  let preset ← presetOf name
  let config ← configOf configName
  let request ← (SigningRequest.ofJson preset document.toJson).mapError requestFault
  let root ← (requestSigningRoot config request).mapError fun fault =>
    (0, s!"root not computed: {reprStr fault}")
  return ⟨root.toArray⟩

/-- The root that a remote signer signs for a request of the Remote-signing API.

The arguments are the name of the preset, the name of the configuration and the document.

The configuration gives the genesis fork version of a registration and of a Builder API request.

An unknown preset or configuration has code 0.

A document that is not a request has the code of its error. -/
@[export eth_consensus_signing_request_root]
def signingRequestRootExport (args : PyValue) : Result PyValue :=
  pyExport signingRequestRootOf args

/-- The secret keys of a signer, each 32 big-endian bytes, or code 0 for a key that is not one. -/
def secretKeysOf (keys : List ByteArray) : Result (List Cryptography.Bls.Signatures.SecretKey) :=
  keys.mapM fun key => (Cryptography.Bls.Signatures.SecretKey.fromBytes key).mapError fun _ =>
    (0, "a secret key is not 32 bytes below the group order, or is zero")

/-- The answer of the sign endpoint of a signer, and its record after the call. -/
def remoteSignerSignOf (args : String × String × List ByteArray × ByteArray × String × PyValue) :
    Result (Nat × Option ByteArray × ByteArray) := do
  let (name, configName, keys, protection, identifier, document) := args
  let preset ← presetOf name
  let config ← configOf configName
  let state : SignerState := ⟨← secretKeysOf keys, ← interchangeOf protection⟩
  let (result, next) := sign preset config eip3076Policy state identifier document.toJson
  let signature := match result with
    | .signed signature => some ⟨signature.toArray⟩
    | _ => none
  return (result.status, signature, interchangeText next.protection)

/-- The answer of the sign endpoint of a remote signer, with the rule of EIP-3076.

The arguments are the preset, the configuration, the secret keys and the record.

Then come the path and the request.

The result is the status, the signature when the status is 200, and the record after the call.

An unknown preset or configuration has code 0.

So do a secret key that is not one and a record that does not read. -/
@[export eth_consensus_remote_signer_sign]
def remoteSignerSignExport (args : PyValue) : Result PyValue :=
  pyExport remoteSignerSignOf args

/-- The answer of the public keys endpoint of a signer that holds some secret keys. -/
def remoteSignerPublicKeysOf (keys : List ByteArray) : Result PyValue := do
  let state : SignerState := ⟨← secretKeysOf keys, ⟨Vector.replicate 32 0, []⟩⟩
  let document ← (publicKeysJson (publicKeys state)).mapError fun fault =>
    (0, s!"keys not written: {reprStr fault}")
  return PyValue.ofJson document

/-- The answer of the public keys endpoint of a remote signer: its public keys as hex.

The argument is the list of its secret keys, each 32 big-endian bytes.

A key that is not one has code 0. -/
@[export eth_consensus_remote_signer_public_keys]
def remoteSignerPublicKeysExport (args : PyValue) : Result PyValue :=
  pyExport remoteSignerPublicKeysOf args

end EthLib.Consensus.Exports
