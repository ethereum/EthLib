module

public import EthLib.Base.Json.Document
public import EthLib.Consensus.BeaconApi.Spelling
public import EthLib.Consensus.SlashingProtection

/-!
# `Consensus.KeymanagerApi.Types`

The values that the calls of the Keymanager API read and write, and their JSON forms.

A management tool sends these values to a validator client, which holds the keys.

The source is the [OpenAPI document] of the Keymanager API, with its [types].

Each reader takes a JSON document and refuses one that the source's schema does not allow.

The reader of a signed voluntary exit is the exception: it is that of the Beacon API.

It also reads an integer from a bare JSON number, and it refuses names that the schema lacks.

Each writer gives the document that its reader reads back, except a keystore, read back rebuilt.

A key and an address are `0x` hex, read in either letter case and written in lowercase.

Two values hold a JSON document as text: a keystore and the slashing protection data.

The slashing protection data reads back from its text.

A keystore reads back from its text as its rebuilt document.

Their readers parse the text, and their writers print the document, with operations they take.

Those operations form a boundary, whose card follows.

- Boundary: these readers and writers use the two operations, and their callers supply them.
  - The production instance is the total JSON reader and the printer of this library, below.
- Owns: the text is a `String`, and the document a `Json` of the Lean toolchain.
- Operations: one parses text into a document, and the other prints a document as text.
- Laws: none for an instance in general.
  - For the production instance, the reader reads back the printed text of a document.
  - That holds when no object of the document repeats a name, and gives each object rebuilt.
- Failure: text that does not parse gives the error of a field that is not JSON.
- Guarantees: the reader of a document receives exactly what the parser gives.
- Assumes: for another instance, the parser reads every text that the printer gives.
- Readings: the source says that each value is JSON serialized, and fixes no form of the text.
  - The printer of the production instance writes compact JSON.

An object may carry names that its schema does not declare, and the readers ignore them.

The reader of a signed voluntary exit, as said above, refuses them.

A name that the schema marks optional may be absent, and its writer leaves it out when unset.

[OpenAPI document]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/keymanager-oapi.yaml
[types]: https://github.com/ethereum/keymanager-APIs/tree/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/types
-/

@[expose] public section

namespace EthLib.Consensus.KeymanagerApi

open Lean Base Cryptography.Bls

/-- Why a value of the Keymanager API does not read. -/
inductive KeymanagerError where
  /-- A field is missing, has the wrong JSON type, or has a value that its schema refuses. -/
  | field (path : String)
  /-- A string that must hold a JSON document holds text that is not JSON. -/
  | notJson (path : String)
  /-- Slashing protection data holds a document that EIP-3076 does not accept. -/
  | slashingProtection (error : SlashingProtectionError)
  deriving DecidableEq, Repr

/-- The code of an error at the C boundary, one for each constructor. -/
def KeymanagerError.code : KeymanagerError → UInt32
  | .field _ => 1
  | .notJson _ => 2
  | .slashingProtection _ => 3

/-- A step of the shared readers of EthLib, with a malformed field kept as such. -/
def ofProtection {α : Type} : Except SlashingProtectionError α → Except KeymanagerError α
  | .ok value => .ok value
  | .error (.field path) => .error (.field path)
  | .error error => .error (.slashingProtection error)

/-! ## Scalars -/

/-- A string: `Graffiti` and `Url` of the [types], and the message of an error.

[types]: https://github.com/ethereum/keymanager-APIs/tree/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/types
-/
def readString (path : String) (document : Json) : Except KeymanagerError String :=
  -- The schema: the type is string, with no pattern.
  ofProtection (Interchange.readString path document)

/-- A 64-bit integer, `Uint64` of [`uint.yaml`], below 2^64.

[`uint.yaml`]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/types/uint.yaml
-/
def readUint64 (path : String) (document : Json) : Except KeymanagerError UInt64 :=
  -- The schema: a string with the pattern ^(0|[1-9][0-9]{0,19})$.
  --
  -- So decimal digits, with no sign and no leading zero.
  --
  -- The pattern admits 20 digits; EthLib refuses a value of 2^64 or more.
  ofProtection (Interchange.readUInt64 path document)

/-- A BLS public key of 48 bytes, from [`public_key.yaml`].

[`public_key.yaml`]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/types/public_key.yaml
-/
def readPubkey (path : String) (document : Json) : Except KeymanagerError BLSPubkey :=
  -- The schema: the pattern ^0x[a-fA-F0-9]{96}$, so 48 bytes.
  ofProtection (Interchange.readBytes path 48 document)

/-- An execution address of 20 bytes, from [`eth_address.yaml`].

The source states no checksum rule for the letter case, so none is checked.

[`eth_address.yaml`]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/types/eth_address.yaml
-/
def readEthAddress (path : String) (document : Json) : Except KeymanagerError ExecutionAddress :=
  -- The schema: the pattern ^0x[a-fA-F0-9]{40}$, so 20 bytes.
  ofProtection (Interchange.readBytes path 20 document)

/-- A BLS signature of 96 bytes, from [`signature.yaml`].

[`signature.yaml`]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/types/signature.yaml
-/
def readSignature (path : String) (document : Json) : Except KeymanagerError BLSSignature :=
  -- The schema: the pattern ^0x[a-fA-F0-9]{192}$, so 96 bytes.
  ofProtection (Interchange.readBytes path 96 document)

/-- A boolean. -/
def readBool (path : String) (document : Json) : Except KeymanagerError Bool :=
  match BeaconApi.ApiEnvelope.readBool document with
  | some flag => .ok flag
  | none => .error (.field path)

/-- An array of strings. -/
def readStrings (path : String) (document : Json) : Except KeymanagerError (List String) :=
  match BeaconApi.ErrorMessage.readStrings document with
  | some texts => .ok texts
  | none => .error (.field path)

/-- A string as the API writes it. -/
def stringJson (text : String) : Json := .str text

/-! ## Documents held as text -/

/-- The two operations on JSON text that a document held as text needs. -/
structure JsonText where
  /-- The document that a text holds, or why it holds none. -/
  parse : String → Except String Json
  /-- The text of a document. -/
  print : Json → String

/-- The total JSON reader and the printer of this library, the instance that the exports use. -/
def jsonText : JsonText := ⟨Base.Json.ofText, Base.Json.toText⟩

/-- A JSON document held as text in a string, read by a reader of the document. -/
def readEmbedded {α : Type} (text : JsonText) (path : String)
    (read : Json → Except KeymanagerError α) (document : Json) : Except KeymanagerError α := do
  -- The schema: a string that holds a JSON serialized document.
  match text.parse (← readString path document) with
  | .ok inner => read inner
  | .error _ => throw (.notJson path)

/-- A JSON document as text in a string. -/
def embeddedJson (text : JsonText) (inner : Json) : Json := .str (text.print inner)

/-- An ERC-2335 keystore, from [`keystore.yaml`]: any JSON document, held as text.

Decryption reads its fields, so this reader asks only for JSON.

[`keystore.yaml`]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/types/keystore.yaml
-/
def readKeystore (text : JsonText) (path : String) (document : Json) :
    Except KeymanagerError Json :=
  -- The schema: a string that holds the JSON of an ERC-2335 keystore; decryption checks its fields.
  readEmbedded text path .ok document

/-- EIP-3076 slashing protection data, from its document, with the error of EIP-3076 kept. -/
def slashingProtectionOfDocument (document : Json) : Except KeymanagerError Interchange :=
  -- The schema: the data in the format of EIP-3076.
  (Interchange.ofJson document).mapError .slashingProtection

/-- EIP-3076 slashing protection data, held as text, from [`slashing_protection.yaml`].

[`slashing_protection.yaml`]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/types/slashing_protection.yaml
-/
def readSlashingProtection (text : JsonText) (path : String) (document : Json) :
    Except KeymanagerError Interchange :=
  readEmbedded text path slashingProtectionOfDocument document

/-- EIP-3076 slashing protection data as the API writes it, as text. -/
def slashingProtectionJson (text : JsonText) (interchange : Interchange) : Json :=
  embeddedJson text interchange.toJson

/-! ## Objects -/

/-- A field of an object, which must be present, read by a reader of its value. -/
def requiredField {α : Type} (path name : String) (read : String → Json → Except KeymanagerError α)
    (document : Json) : Except KeymanagerError α := do
  -- The schema: a required property is present.
  read s!"{path}.{name}" (← ofProtection (Interchange.field path name document))

/-- A field of an object, which may be absent, read by a reader of its value. -/
def optionalField {α : Type} (path name : String) (read : String → Json → Except KeymanagerError α)
    (document : Json) : Except KeymanagerError (Option α) :=
  -- The schema: an optional property may be absent; when present, it must read.
  match document.getObjVal? name with
  | .ok value => do return some (← read s!"{path}.{name}" value)
  | .error _ => .ok none

/-- The field of an optional value, none when it is unset. -/
def optionalFields {α : Type} (name : String) (write : α → Json) : Option α → List (String × Json)
  -- An unset optional property is left out.
  | some value => [(name, write value)]
  | none => []

/-- The definition of a remote key, from [`signer_definition.yaml`].

[`signer_definition.yaml`]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/types/signer_definition.yaml
-/
structure SignerDefinition where
  /-- The public key. -/
  pubkey : BLSPubkey
  /-- The address of the EIP-3030 remote signer that holds the key, if given. -/
  url : Option String
  /-- Whether the key cannot be deleted through the API, if given. -/
  readonly : Option Bool
  deriving DecidableEq, Repr

/-- A remote key to import, from [`import_remote_signer_definition.yaml`].

[`import_remote_signer_definition.yaml`]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/types/import_remote_signer_definition.yaml
-/
structure ImportRemoteSignerDefinition where
  /-- The public key. -/
  pubkey : BLSPubkey
  /-- The address of the EIP-3030 remote signer that holds the key, if given. -/
  url : Option String
  deriving DecidableEq, Repr

/-- The address that receives the fees of a proposer, from [`fee_recipient.yaml`].

[`fee_recipient.yaml`]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/types/fee_recipient.yaml
-/
structure FeeRecipient where
  /-- The public key of the validator, if given. -/
  pubkey : Option BLSPubkey
  /-- The address. -/
  ethaddress : ExecutionAddress
  deriving DecidableEq, Repr

/-- The gas limit that a proposer asks of an external builder, from [`gas_limit.yaml`].

[`gas_limit.yaml`]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/types/gas_limit.yaml
-/
structure GasLimit where
  /-- The public key of the validator, if given. -/
  pubkey : Option BLSPubkey
  /-- The gas limit. -/
  gasLimit : UInt64
  deriving DecidableEq, Repr

/-- The body of an error response, from [`error_response.yaml`].

[`error_response.yaml`]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/types/error_response.yaml
-/
structure ErrorResponse where
  /-- What went wrong. -/
  message : String
  deriving DecidableEq, Repr

/-- The definition of a remote key, from its object. -/
def readSignerDefinition (path : String) (document : Json) :
    Except KeymanagerError SignerDefinition := do
  -- The schema: the public key is required; the URL and the read-only flag are optional.
  return {
    pubkey := ← requiredField path "pubkey" readPubkey document
    url := ← optionalField path "url" readString document
    readonly := ← optionalField path "readonly" readBool document }

/-- The definition of a remote key as the API writes it. -/
def signerDefinitionJson (definition : SignerDefinition) : Json :=
  Json.mkObj ([("pubkey", Interchange.bytesJson definition.pubkey)] ++
    optionalFields "url" stringJson definition.url ++
    optionalFields "readonly" Json.bool definition.readonly)

/-- A remote key to import, from its object. -/
def readImportRemoteSignerDefinition (path : String) (document : Json) :
    Except KeymanagerError ImportRemoteSignerDefinition := do
  -- The schema: the public key is required, and the URL is optional.
  return {
    pubkey := ← requiredField path "pubkey" readPubkey document
    url := ← optionalField path "url" readString document }

/-- A remote key to import as the API writes it. -/
def importRemoteSignerDefinitionJson (definition : ImportRemoteSignerDefinition) : Json :=
  Json.mkObj ([("pubkey", Interchange.bytesJson definition.pubkey)] ++
    optionalFields "url" stringJson definition.url)

/-- A fee recipient, from its object. -/
def readFeeRecipient (path : String) (document : Json) : Except KeymanagerError FeeRecipient := do
  -- The schema: the address is required, and the public key is optional.
  return {
    pubkey := ← optionalField path "pubkey" readPubkey document
    ethaddress := ← requiredField path "ethaddress" readEthAddress document }

/-- A fee recipient as the API writes it. -/
def feeRecipientJson (recipient : FeeRecipient) : Json :=
  Json.mkObj (optionalFields "pubkey" Interchange.bytesJson recipient.pubkey ++
    [("ethaddress", Interchange.bytesJson recipient.ethaddress)])

/-- A gas limit, from its object. -/
def readGasLimit (path : String) (document : Json) : Except KeymanagerError GasLimit := do
  -- The schema: the gas limit is required, and the public key is optional.
  return {
    pubkey := ← optionalField path "pubkey" readPubkey document
    gasLimit := ← requiredField path "gas_limit" readUint64 document }

/-- A gas limit as the API writes it. -/
def gasLimitJson (limit : GasLimit) : Json :=
  Json.mkObj (optionalFields "pubkey" Interchange.bytesJson limit.pubkey ++
    [("gas_limit", Interchange.uint64Json limit.gasLimit)])

/-- The body of an error response, from its object. -/
def readErrorResponse (path : String) (document : Json) : Except KeymanagerError ErrorResponse := do
  -- The schema: the message is required.
  return { message := ← requiredField path "message" readString document }

/-- The body of an error response as the API writes it. -/
def errorResponseJson (response : ErrorResponse) : Json :=
  Json.mkObj [("message", stringJson response.message)]

/-- A signed voluntary exit, from [`voluntary_exit.yaml`].

Its JSON is that of the Beacon API: the epoch and the index in decimal, the signature in hex.

That reader also takes an integer as a bare JSON number, and refuses a name it does not declare.

It requires every field, where the source lists none as required, since the container has all.

[`voluntary_exit.yaml`]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/types/voluntary_exit.yaml
-/
def readSignedVoluntaryExit (path : String) (document : Json) :
    Except KeymanagerError SignedVoluntaryExit :=
  -- EthLib reads it with the reader of the Beacon API, with the departures listed above.
  (BeaconApi.ofApiJson SignedVoluntaryExit document).mapError fun _ => .field path

/-- A signed voluntary exit as the API writes it.

The writer of the Beacon API can fail in its type, so this one can too; it never does. -/
def signedVoluntaryExitJson (signed : SignedVoluntaryExit) : Except KeymanagerError Json :=
  (BeaconApi.toApiJson signed).mapError fun _ => .field ""

/-! ## Requests -/

/-- A request to delete keys, local or remote. -/
structure DeleteKeysRequest where
  /-- The keys to delete, in order. -/
  pubkeys : List BLSPubkey
  deriving DecidableEq, Repr

/-- An array of public keys, each read in turn. -/
def readPubkeys (path : String) (document : Json) : Except KeymanagerError (List BLSPubkey) :=
  -- The schema: an array whose items are public keys.
  ofProtection (Interchange.readArray path (fun path => Interchange.readBytes path 48) document)

/-- A request to delete keys, from its object. -/
def readDeleteKeysRequest (document : Json) : Except KeymanagerError DeleteKeysRequest := do
  -- The schema of the request body: the public keys are required.
  return { pubkeys := ← requiredField "" "pubkeys" readPubkeys document }

/-! ## Responses -/

/-- A response of the API: its HTTP status code and its JSON body. -/
structure Response where
  /-- The HTTP status code. -/
  status : Nat
  /-- The JSON body. -/
  body : Json

/-- A response with HTTP 400 and the body of an error. -/
def badRequest (message : String) : Response :=
  -- The source: a request that was malformed and could not be processed, with an error body.
  ⟨400, errorResponseJson ⟨message⟩⟩

end EthLib.Consensus.KeymanagerApi
