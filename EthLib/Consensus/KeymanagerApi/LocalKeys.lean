module

public import EthLib.Consensus.KeymanagerApi.Client

/-!
# `Consensus.KeymanagerApi.LocalKeys`

The call of the Keymanager API that imports keystores into a validator client.

A management tool sends ERC-2335 keystores, their passwords, and EIP-3076 slashing protection data.

The call is `POST /eth/v1/keystores` of [`local_keystores.yaml`], by the steps of the [import flow].

A request whose lists of keystores and passwords differ in length is refused with HTTP 400.

So is a request whose slashing protection data does not read, unless it sends no keystore.

Otherwise the call answers with one status for each keystore, in order, with HTTP 200.

A keystore is imported when it decrypts to a BLS secret key whose public key is not active.

A key already active, or imported earlier in the same request, is a duplicate.

Any other failure gives an error status, and does not stop the other keystores.

An imported key brings the entries of the slashing protection data that name it, and no others.

They enter the record of the client by the minimal strategy of EIP-3076.

The [use cases] say that the data of keys that are not imported is imported too.

Step 3 of the import flow allows either, and its step 4 loads data only for a matching keystore.

This module takes the reading of step 4; `SOUNDNESS.md` records the question.

So the data of a keystore that is a duplicate is not loaded either.

[`local_keystores.yaml`]: https://github.com/ethereum/keymanager-APIs/blob/51f2a5c90e9d301c3e9980da402ec70ae82f0991/apis/local_keystores.yaml
[import flow]: https://github.com/ethereum/keymanager-APIs/blob/51f2a5c90e9d301c3e9980da402ec70ae82f0991/flows/README.md#import
[use cases]: https://github.com/ethereum/keymanager-APIs/blob/51f2a5c90e9d301c3e9980da402ec70ae82f0991/use-cases/README.md#add-a-key
-/

@[expose] public section

namespace EthLib.Consensus.KeymanagerApi

open Lean Base Cryptography Cryptography.Bls

/-! ## The request -/

/-- A request to import keystores. -/
structure ImportKeystoresRequest where
  /-- The keystores, each an ERC-2335 document held as text. -/
  keystores : List String
  /-- The password of each keystore, at the same position. -/
  passwords : List String
  /-- The slashing protection data, if sent, or why it does not read.

  A request with no keystore succeeds even when the data does not read, so the error waits. -/
  slashingProtection : Option (Except KeymanagerError Interchange)

/-- A request to import keystores, from its object.

The two lists are required, and the slashing protection data may be absent. -/
def readImportKeystoresRequest (text : JsonText) (document : Json) :
    Except KeymanagerError ImportKeystoresRequest := do
  return {
    keystores := ← requiredField "" "keystores" readStrings document
    passwords := ← requiredField "" "passwords" readStrings document
    slashingProtection := (document.getObjVal? "slashing_protection").toOption.map
      (readSlashingProtection text ".slashing_protection") }

/-! ## The call -/

/-- The status of one keystore of a request. -/
inductive ImportStatus where
  /-- The keystore decrypted to a key that was not active, and the key is now active. -/
  | imported
  /-- The keystore decrypted to a key that was already active. -/
  | duplicate
  /-- The keystore did not decrypt to a key, for the reason given. -/
  | error (message : String)
  deriving DecidableEq, Repr

/-- Why a request to import keystores is refused as a whole, with HTTP 400. -/
inductive ImportKeystoresError where
  /-- The lists of keystores and passwords differ in length. -/
  | lengthMismatch (keystores passwords : Nat)
  /-- The slashing protection data does not read. -/
  | slashingProtection (error : KeymanagerError)
  deriving DecidableEq, Repr

/-- The key that a keystore holds, decrypted with its password.

The public key is derived from the secret key; the `pubkey` field of the keystore is not read. -/
def decodeKeystore (text : JsonText) (limits : Keystore.KdfLimits) (keystore password : String) :
    Except String LocalKey := do
  let .ok document := readKeystore text "" (.str keystore) | throw "the keystore is not JSON"
  let secret ← (Keystore.decrypt limits document password).mapError fun e =>
    s!"the keystore did not decrypt, with code {e.code}"
  let secretKey ← (Signatures.SecretKey.fromBytes secret).mapError fun _ =>
    "the secret is not a BLS secret key"
  -- Decryption has checked that the path is a string.
  let derivationPath := ((document.getObjVal? "path").bind Json.getStr?).toOption.getD ""
  return { pubkey := Signatures.skToPk secretKey, secretKey, derivationPath, readonly := false }

/-- The record after a key is imported with the entries of the data that name it.

The record is unchanged when no data is sent, or when the data names the key nowhere. -/
def loadProtection (file : Option Interchange) (pubkey : BLSPubkey) (held : Interchange) :
    Interchange :=
  match file with
  | some file =>
    let own := file.entriesOf [pubkey]
    -- Importing no entry would still prune the record to its minimal form, so it is skipped.
    if own.data.isEmpty then held else held.importFile own
  | none => held

/-- The status of one keystore and the state after it. -/
def importKeystore (text : JsonText) (limits : Keystore.KdfLimits) (file : Option Interchange)
    (state : KeyState) (keystore password : String) : ImportStatus × KeyState :=
  match decodeKeystore text limits keystore password with
  | .error message => (.error message, state)
  | .ok key =>
    if state.isActive key.pubkey then (.duplicate, state)
    else
      (.imported, { state with
        localKeys := state.localKeys ++ [key]
        protection := loadProtection file key.pubkey state.protection })

/-- The statuses of keystores and their passwords, in order, and the state after the last. -/
def importAll (text : JsonText) (limits : Keystore.KdfLimits) (file : Option Interchange) :
    KeyState → List (String × String) → List ImportStatus × KeyState
  | state, [] => ([], state)
  | state, (keystore, password) :: rest =>
    let (status, state) := importKeystore text limits file state keystore password
    let (statuses, state) := importAll text limits file state rest
    (status :: statuses, state)

/-- The call `POST /eth/v1/keystores`: the status of each keystore and the state after them.

The limits bound the key derivation of each keystore, since the source does not.

The text operations parse each keystore. -/
def importKeystores (text : JsonText) (limits : Keystore.KdfLimits) (state : KeyState)
    (request : ImportKeystoresRequest) :
    Except ImportKeystoresError (List ImportStatus × KeyState) := do
  unless request.keystores.length = request.passwords.length do
    throw (.lengthMismatch request.keystores.length request.passwords.length)
  if request.keystores.isEmpty then return ([], state)
  let file ← match request.slashingProtection with
    | some (.ok data) => pure (some data)
    | some (.error error) => throw (.slashingProtection error)
    | none => pure none
  return importAll text limits file state (request.keystores.zip request.passwords)

/-! ## The response -/

/-- The status of one keystore as the API writes it. -/
def importStatusJson : ImportStatus → Json
  | .imported => Json.mkObj [("status", "imported")]
  | .duplicate => Json.mkObj [("status", "duplicate")]
  | .error message => Json.mkObj [("status", "error"), ("message", .str message)]

/-- The body of the response, with HTTP 200. -/
def importResponseJson (statuses : List ImportStatus) : Json :=
  Json.mkObj [("data", .arr (statuses.map importStatusJson).toArray)]

/-- The call `POST /eth/v1/keystores` on the body of a request, and the state after it.

A body that does not read is refused with HTTP 400, and the state does not change. -/
def postKeystores (text : JsonText) (limits : Keystore.KdfLimits) (state : KeyState)
    (body : Json) : Response × KeyState :=
  match readImportKeystoresRequest text body with
  | .error _ => (badRequest "the request does not read", state)
  | .ok request =>
    match importKeystores text limits state request with
    | .error (.lengthMismatch _ _) =>
      (badRequest "the keystores and the passwords differ in number", state)
    | .error (.slashingProtection _) =>
      (badRequest "the slashing protection data does not read", state)
    | .ok (statuses, state) => (⟨200, importResponseJson statuses⟩, state)

end EthLib.Consensus.KeymanagerApi
