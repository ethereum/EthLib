module

public import EthLib.Consensus.RemoteSigningApi.SigningRoot
public import EthLib.Consensus.Exports.Parameters

/-!
# `Exports.RemoteSigningApi`

C-ABI exports of the Remote-signing API: the requests that a remote signer reads, and their roots.

A request comes as a JSON document, and one export writes it again as the signer reads it.

The other gives the root that the signer signs for it.

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

end EthLib.Consensus.Exports
