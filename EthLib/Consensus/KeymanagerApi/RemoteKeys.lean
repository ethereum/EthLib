module

public import EthLib.Consensus.KeymanagerApi.DeleteKeys
public import EthLib.Consensus.KeymanagerApi.LocalKeys

/-!
# `Consensus.KeymanagerApi.RemoteKeys`

The calls of the Keymanager API on the keys that a client signs with through a remote signer.

They are `GET`, `POST` and `DELETE` on `/eth/v1/remotekeys` of [`remote_keystores.yaml`].

The source lists an error status for I/O errors, which a pure state never meets.

[`remote_keystores.yaml`]: https://github.com/ethereum/keymanager-APIs/blob/2d8a02843cbf91f7ebc6274bf68a89b908019130/apis/remote_keystores.yaml
-/

@[expose] public section

namespace EthLib.Consensus.KeymanagerApi

open Lean Base Cryptography.Bls

/-! ## Listing -/

/-- The call `GET /eth/v1/remotekeys`: every remote key, in order. -/
def listRemoteKeys (state : KeyState) : List SignerDefinition :=
  -- The source: all remote keys known to the client, here in the order of import.
  state.remoteKeys

/-- The body of the response that lists the remote keys, with HTTP 200. -/
def listRemoteKeysJson (keys : List SignerDefinition) : Json :=
  -- The response schema: the signer definitions under data.
  Json.mkObj [("data", .arr (keys.map signerDefinitionJson).toArray)]

/-- The call `GET /eth/v1/remotekeys`, with HTTP 200, which leaves the state as it was. -/
def getRemoteKeys (state : KeyState) : Response × KeyState :=
  (⟨200, listRemoteKeysJson (listRemoteKeys state)⟩, state)

/-! ## Importing -/

/-- Whether a key is known to the client: held locally, or a remote key. -/
def KeyState.isKnown (state : KeyState) (pubkey : BLSPubkey) : Bool :=
  -- The source: already known to the client; EthLib reads a key held locally as known too.
  state.isActive pubkey || state.remoteKeys.any (·.pubkey == pubkey)

/-- A request to import remote keys, from its object. -/
def readImportRemoteKeysRequest (document : Json) :
    Except KeymanagerError (List ImportRemoteSignerDefinition) :=
  -- The schema of the request body: a required array of remote keys to import.
  requiredField "" "remote_keys"
    (fun path value => ofProtection (Interchange.readArray path
      (fun path value => match readImportRemoteSignerDefinition path value with
        | .ok definition => .ok definition
        | .error _ => .error (.field path)) value)) document

/-- The status of one remote key and the state after it.

An imported key can be deleted through the API. -/
def importRemoteKey (state : KeyState) (definition : ImportRemoteSignerDefinition) :
    ImportStatus × KeyState :=
  -- The source: a key already known gets status duplicate.
  --
  -- A key imported earlier in the request is known, so it is a duplicate too.
  if state.isKnown definition.pubkey then (.duplicate, state)
  else
    -- The source: status imported.
    --
    -- EthLib adds the key after the others, and marks it as one that can be deleted.
    (.imported, { state with
      remoteKeys := state.remoteKeys ++
        [{ pubkey := definition.pubkey, url := definition.url, readonly := some false }] })

/-- The call `POST /eth/v1/remotekeys`: the status of each key, in order, and the state after. -/
def importRemoteKeys : KeyState → List ImportRemoteSignerDefinition → List ImportStatus × KeyState
  | state, [] => ([], state)
  -- The source: one status for each key, in the length and order of the request.
  | state, definition :: rest =>
    let (status, state) := importRemoteKey state definition
    let (statuses, state) := importRemoteKeys state rest
    (status :: statuses, state)

/-! ## Deleting -/

/-- The status of one remote key of a request to delete them, and the state after it. -/
def deleteRemoteKey (state : KeyState) (pubkey : BLSPubkey) : DeleteStatus × KeyState :=
  -- The source: a read-only remote key cannot be deleted from the API, and gets no status.
  --
  -- EthLib's choice: it stays, with status error, as a local one does.
  if state.remoteKeys.any (fun key => key.pubkey == pubkey && key.readonly == some true) then
    (.error "the key is read-only", state)
  -- The source: a remote key known to the client is removed, with status deleted.
  else if state.remoteKeys.any (·.pubkey == pubkey) then
    (.deleted, { state with remoteKeys := state.remoteKeys.filter (·.pubkey != pubkey) })
  -- The source: any other key gets status not found.
  --
  -- EthLib's choice: a local key also gets it here, since this call deletes only remote keys.
  else (.notFound, state)

/-- The call `DELETE /eth/v1/remotekeys`: the status of each key, in order, and the state after. -/
def deleteRemoteKeys : KeyState → List BLSPubkey → List DeleteStatus × KeyState
  | state, [] => ([], state)
  -- The source: one status for each key, in the order of the request.
  | state, pubkey :: rest =>
    let (status, state) := deleteRemoteKey state pubkey
    let (statuses, state) := deleteRemoteKeys state rest
    (status :: statuses, state)

/-! ## The calls on their bodies -/

/-- The call `POST /eth/v1/remotekeys` on the body of a request, and the state after it. -/
def postRemoteKeys (state : KeyState) (body : Json) : Response × KeyState :=
  match readImportRemoteKeysRequest body with
  -- The source lists no HTTP 400 here; EthLib gives it, as for the other calls.
  | .error _ => (badRequest "the request does not read", state)
  | .ok definitions =>
    let (statuses, state) := importRemoteKeys state definitions
    -- The source: HTTP 200, with the statuses under data.
    (⟨200, importResponseJson statuses⟩, state)

/-- The call `DELETE /eth/v1/remotekeys` on the body of a request, and the state after it.

Any body that reads gets HTTP 200, never 404. -/
def deleteRemoteKeysCall (state : KeyState) (body : Json) : Response × KeyState :=
  match readDeleteKeysRequest body with
  -- The source lists no HTTP 400 here; EthLib gives it, as for the other calls.
  | .error _ => (badRequest "the request does not read", state)
  | .ok request =>
    let (statuses, state) := deleteRemoteKeys state request.pubkeys
    -- The source: HTTP 200, with the statuses under data; it should never be 404.
    (⟨200, Json.mkObj [("data", .arr (statuses.map deleteStatusJson).toArray)]⟩, state)

end EthLib.Consensus.KeymanagerApi
