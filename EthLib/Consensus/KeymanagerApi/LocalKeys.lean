module

public import EthLib.Consensus.KeymanagerApi.Client

/-!
# `Consensus.KeymanagerApi.LocalKeys`

The call of the Keymanager API that imports keystores into a validator client.

A management tool sends ERC-2335 keystores, their passwords, and EIP-3076 slashing protection data.

The call is `POST /eth/v1/keystores` of [`local_keystores.yaml`], by the steps of the [import flow].

The [use cases] say that the data of keys that are not imported is imported too.

Step 3 of the import flow allows either, and its step 4 loads data only for a matching keystore.

This module takes the reading of step 4; `SOUNDNESS.md` records the question.

[`local_keystores.yaml`]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/apis/local_keystores.yaml
[import flow]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/flows/README.md#import
[use cases]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/use-cases/README.md#add-a-key
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
  -- The schema of the request body: keystores and passwords are required arrays of strings.
  --
  -- The slashing protection data is optional, and its error waits for the call.
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

The public key is derived from the secret key.

Decryption checks only the form of the `pubkey` field of the keystore. -/
def decodeKeystore (text : JsonText) (limits : Keystore.KdfLimits) (keystore password : String) :
    Except String LocalKey := do
  -- The schema: a keystore is the JSON of an ERC-2335 keystore, serialized in a string.
  let .ok document := readKeystore text "" (.str keystore) | throw "the keystore is not JSON"
  -- Flow, step 4: decode and verify the keystore and password combination, else status error.
  let secret ← (Keystore.decrypt limits document password).mapError fun e =>
    s!"the keystore did not decrypt, with code {e.code}"
  -- EthLib reads the verify of step 4 as: the secret is a BLS secret key, else status error.
  let secretKey ← (Signatures.SecretKey.fromBytes secret).mapError fun _ =>
    "the secret is not a BLS secret key"
  -- Decryption has checked that the path is a string: an ERC-2334 path, or empty.
  let derivationPath := ((document.getObjVal? "path").bind Json.getStr?).toOption.getD ""
  -- The public key comes from the secret key; EthLib's choice: an imported key is not read-only.
  return { pubkey := Signatures.skToPk secretKey, secretKey, derivationPath, readonly := false }

/-- The record after a key is imported with the entries of the data that name it.

The record is unchanged when no data is sent, or when the data names the key nowhere. -/
def loadProtection (file : Option Interchange) (pubkey : BLSPubkey) (held : Interchange) :
    Interchange :=
  match file with
  -- Flow, step 4: load the slashing protection data for this key, if supplied.
  | some file =>
    -- The entries of the data that name the key, and no others.
    let own := file.entriesOf [pubkey]
    -- They enter the record by the minimal strategy of EIP-3076.
    --
    -- The import of the data is pure, so the error of step 4 for a failed import never occurs.
    --
    -- Importing no entry would still prune the record to its minimal form, so it is skipped.
    if own.data.isEmpty then held else held.importFile own
  -- No data sent: the record stays.
  | none => held

/-- The status of one keystore and the state after it. -/
def importKeystore (text : JsonText) (limits : Keystore.KdfLimits) (file : Option Interchange)
    (state : KeyState) (keystore password : String) : ImportStatus × KeyState :=
  match decodeKeystore text limits keystore password with
  -- Flow, step 4: a keystore that does not decrypt to a key gets status error.
  | .error message => (.error message, state)
  | .ok key =>
    -- Flow, step 4: verify that the key is not active, else status duplicate.
    --
    -- A key imported earlier in the request is active, so it is a duplicate, as the use cases say.
    --
    -- The data of a duplicate is not loaded: step 4 loads it only for a key that is not active.
    if state.isActive key.pubkey then (.duplicate, state)
    else
      -- Flow, step 4: the key enters the active keys, after the data that names it.
      --
      -- Storage, and its failures, are left to each client.
      (.imported, { state with
        localKeys := state.localKeys ++ [key]
        protection := loadProtection file key.pubkey state.protection })

/-- The statuses of keystores and their passwords, in order, and the state after the last. -/
def importAll (text : JsonText) (limits : Keystore.KdfLimits) (file : Option Interchange) :
    KeyState → List (String × String) → List ImportStatus × KeyState
  | state, [] => ([], state)
  -- Flow, step 4: each keystore in turn, and a failure does not stop the batch.
  | state, (keystore, password) :: rest =>
    let (status, state) := importKeystore text limits file state keystore password
    let (statuses, state) := importAll text limits file state rest
    -- Flow, step 5: the statuses in the order of the keystores.
    (status :: statuses, state)

/-- The call `POST /eth/v1/keystores`: the status of each keystore and the state after them.

The limits bound the key derivation of each keystore, since the source does not.

The text operations parse each keystore. -/
def importKeystores (text : JsonText) (limits : Keystore.KdfLimits) (state : KeyState)
    (request : ImportKeystoresRequest) :
    Except ImportKeystoresError (List ImportStatus × KeyState) := do
  -- Flow, step 1: the lists of keystores and passwords have the same length, else HTTP 400.
  unless request.keystores.length = request.passwords.length do
    throw (.lengthMismatch request.keystores.length request.passwords.length)
  -- Flow, step 2: blank lists give HTTP 200, with no status.
  --
  -- The flow lets a client read the data and fail on it here; EthLib's choice does not.
  if request.keystores.isEmpty then return ([], state)
  -- Flow, step 3: slashing protection data that is present and does not read is an HTTP 400.
  let file ← match request.slashingProtection with
    | some (.ok data) => pure (some data)
    | some (.error error) => throw (.slashingProtection error)
    | none => pure none
  -- Flow, step 4: the batch over the pairs of a keystore and its password.
  return importAll text limits file state (request.keystores.zip request.passwords)

/-! ## The response -/

/-- The status of one keystore as the API writes it. -/
def importStatusJson : ImportStatus → Json
  -- The response schema: a status of imported, duplicate or error, with a message for an error.
  | .imported => Json.mkObj [("status", "imported")]
  | .duplicate => Json.mkObj [("status", "duplicate")]
  | .error message => Json.mkObj [("status", "error"), ("message", .str message)]

/-- The body of the response, with HTTP 200. -/
def importResponseJson (statuses : List ImportStatus) : Json :=
  -- The response schema: the statuses under data, in the length and order of the keystores.
  Json.mkObj [("data", .arr (statuses.map importStatusJson).toArray)]

/-- The call `POST /eth/v1/keystores` on the body of a request, and the state after it.

A body that does not read is refused with HTTP 400, and the state does not change. -/
def postKeystores (text : JsonText) (limits : Keystore.KdfLimits) (state : KeyState)
    (body : Json) : Response × KeyState :=
  match readImportKeystoresRequest text body with
  -- The source: a malformed request gets HTTP 400.
  | .error _ => (badRequest "the request does not read", state)
  | .ok request =>
    match importKeystores text limits state request with
    -- Flow, steps 1 and 3: HTTP 400, with the state unchanged.
    | .error (.lengthMismatch _ _) =>
      (badRequest "the keystores and the passwords differ in number", state)
    | .error (.slashingProtection _) =>
      (badRequest "the slashing protection data does not read", state)
    -- Flow, step 5: after step 3, the response is HTTP 200 with the batch results.
    | .ok (statuses, state) => (⟨200, importResponseJson statuses⟩, state)

end EthLib.Consensus.KeymanagerApi
