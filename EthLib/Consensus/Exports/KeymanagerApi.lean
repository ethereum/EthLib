module

public import EthLib.Base.Exports.PyValue
public import EthLib.Consensus.KeymanagerApi.Types

/-!
# `Exports.KeymanagerApi`

C-ABI exports of the Keymanager API.

A value is named by its schema in the source, and travels as a Python value: strings and objects.

A value that does not read has the code of its error.

A name that the source does not give a schema has code 0.
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

end EthLib.Consensus.Exports
