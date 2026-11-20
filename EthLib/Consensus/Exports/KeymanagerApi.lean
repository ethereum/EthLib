module

public import EthLib.Base.Exports.PyValue
public import EthLib.Consensus.KeymanagerApi.Server

/-!
# `Exports.KeymanagerApi`

C-ABI exports of the Keymanager API.

A value is named by its schema in the source, and travels as a Python value: strings and objects.

A value that does not read has the code of its error.

A name that the source does not give a schema has code 0.

Calls run one after another on a validator client that starts with no key and a given record.

A call is named by its method and its path; one that the API lacks gets HTTP 404.
-/

public section

namespace EthLib.Consensus.Exports

open Lean KeymanagerApi
open EthLib.Exports (Result PyValue pyExport)

/-- The result of a step of the Keymanager API, with the code of its error. -/
def runKeymanager {α : Type} (result : Except KeymanagerError α) : Result α :=
  result.mapError fun e => (e.code, s!"keymanager value rejected with code {e.code}")

/-- The JSON parser and printer of the Lean toolchain, which the exports supply to the API. -/
def toolchainJsonText : JsonText := ⟨Json.parse, Json.compress⟩

/-- A value of a schema of the Keymanager API, read from its JSON and written back. -/
def keymanagerJsonOf (args : String × PyValue) : Result PyValue := do
  let (schema, document) := args
  let document := document.toJson
  let written ← match schema with
    | "Pubkey" => runKeymanager do return Interchange.bytesJson (← readPubkey "" document)
    | "EthAddress" => runKeymanager do return Interchange.bytesJson (← readEthAddress "" document)
    | "Uint64" => runKeymanager do return Interchange.uint64Json (← readUint64 "" document)
    | "Graffiti" | "Url" => runKeymanager do return stringJson (← readString "" document)
    | "Signature" => runKeymanager do return Interchange.bytesJson (← readSignature "" document)
    | "Keystore" =>
      runKeymanager do
        return embeddedJson toolchainJsonText (← readKeystore toolchainJsonText "" document)
    | "SlashingProtectionData" =>
      runKeymanager do
        return slashingProtectionJson toolchainJsonText
          (← readSlashingProtection toolchainJsonText "" document)
    | "SignerDefinition" =>
      runKeymanager do return signerDefinitionJson (← readSignerDefinition "" document)
    | "ImportRemoteSignerDefinition" =>
      runKeymanager do
        return importRemoteSignerDefinitionJson (← readImportRemoteSignerDefinition "" document)
    | "FeeRecipient" => runKeymanager do return feeRecipientJson (← readFeeRecipient "" document)
    | "GasLimit" => runKeymanager do return gasLimitJson (← readGasLimit "" document)
    | "ErrorResponse" =>
      runKeymanager do return errorResponseJson (← readErrorResponse "" document)
    | "SignedVoluntaryExit" =>
      runKeymanager do signedVoluntaryExitJson (← readSignedVoluntaryExit "" document)
    | _ => throw (0, s!"the Keymanager API has no schema {schema}")
  return PyValue.ofJson written

/-- A value of a schema of the Keymanager API, read from its JSON and written back.

The arguments are the name of the schema in the source, such as `Pubkey`, and the value.

Hex is written in lowercase, and a document held as text is printed in compact form. -/
@[export eth_consensus_keymanager_json]
def keymanagerJsonExport (args : PyValue) : Result PyValue := pyExport keymanagerJsonOf args

/-! ## Calls on a validator client -/

/-- The state of a client as the export gives it: its record as JSON text and its keys. -/
def keyStateJson (state : KeyState) : Json :=
  Json.mkObj [
    ("slashing_protection", slashingProtectionJson toolchainJsonText state.protection),
    ("local_keys", .arr (state.localKeys.map fun key =>
      Interchange.bytesJson key.pubkey).toArray)]

/-- The responses of calls made one after another on a client, then its state. -/
def keymanagerRunOf (args : Nat × Nat × String × List (String × String × PyValue)) :
    Result (List (Nat × PyValue) × PyValue) := do
  let (memory, work, protection, calls) := args
  let config : ClientConfig := { limits := { memory, work } }
  let record ← runKeymanager
    (readSlashingProtection toolchainJsonText "" (.str protection))
  let start : KeyState := { localKeys := [], remoteKeys := [], protection := record }
  let (responses, state) := calls.foldl (init := ([], start)) fun (responses, state) call =>
    let (method, path, body) := call
    let (response, state) := handle toolchainJsonText config state method path body.toJson
    ((response.status, PyValue.ofJson response.body) :: responses, state)
  return (responses.reverse, PyValue.ofJson (keyStateJson state))

/-- The responses of calls made one after another on a validator client, then its state.

The arguments are the memory and work bounds of key derivation, and the record as JSON text.

The calls follow, each its method, its path and its body.

The client starts with no key, and each call sees the state that the one before it left.

The result gives the status code and body of each response, then the record and the keys held. -/
@[export eth_consensus_keymanager_run]
def keymanagerRunExport (args : PyValue) : Result PyValue := pyExport keymanagerRunOf args

end EthLib.Consensus.Exports
