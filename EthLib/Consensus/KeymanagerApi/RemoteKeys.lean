module

public import EthLib.Consensus.KeymanagerApi.DeleteKeys
public import EthLib.Consensus.KeymanagerApi.LocalKeys

/-!
# `Consensus.KeymanagerApi.RemoteKeys`

The calls of the Keymanager API on the keys that a client signs with through a remote signer.

They are `GET`, `POST` and `DELETE` on `/eth/v1/remotekeys` of [`remote_keystores.yaml`].

The list gives every remote key, in order.

An import adds each key of the request that is not "already known to the validator client".

A key held locally is known too, so it is a duplicate, as is a key imported earlier in the request.

A delete removes each key of the request that is a remote key, and gives not found for any other.

The source lists an error status for "I/O errors", which a pure state never meets.

A remote key marked read-only stays, with an error status, as a local one does.

A body that does not read gets HTTP 400, as for the other calls, though the source lists none here.

[`remote_keystores.yaml`]: https://github.com/ethereum/keymanager-APIs/blob/51f2a5c90e9d301c3e9980da402ec70ae82f0991/apis/remote_keystores.yaml
-/

@[expose] public section

namespace EthLib.Consensus.KeymanagerApi

open Lean Base Cryptography.Bls

/-! ## Listing -/

/-- The call `GET /eth/v1/remotekeys`: every remote key, in order. -/
def listRemoteKeys (state : KeyState) : List SignerDefinition :=
  state.remoteKeys

/-- The body of the response that lists the remote keys, with HTTP 200. -/
def listRemoteKeysJson (keys : List SignerDefinition) : Json :=
  Json.mkObj [("data", .arr (keys.map signerDefinitionJson).toArray)]

/-- The call `GET /eth/v1/remotekeys`, with HTTP 200, which leaves the state as it was. -/
def getRemoteKeys (state : KeyState) : Response × KeyState :=
  (⟨200, listRemoteKeysJson (listRemoteKeys state)⟩, state)

/-! ## Importing -/

/-- Whether a key is known to the client: held locally, or a remote key. -/
def KeyState.isKnown (state : KeyState) (pubkey : BLSPubkey) : Bool :=
  state.isActive pubkey || state.remoteKeys.any (·.pubkey == pubkey)

/-- A request to import remote keys, from its object. -/
def readImportRemoteKeysRequest (document : Json) :
    Except KeymanagerError (List ImportRemoteSignerDefinition) :=
  requiredField "" "remote_keys"
    (fun path value => ofProtection (Interchange.readArray path
      (fun path value => match readImportRemoteSignerDefinition path value with
        | .ok definition => .ok definition
        | .error _ => .error (.field path)) value)) document

/-- The status of one remote key and the state after it.

An imported key can be deleted through the API. -/
def importRemoteKey (state : KeyState) (definition : ImportRemoteSignerDefinition) :
    ImportStatus × KeyState :=
  if state.isKnown definition.pubkey then (.duplicate, state)
  else
    (.imported, { state with
      remoteKeys := state.remoteKeys ++
        [{ pubkey := definition.pubkey, url := definition.url, readonly := some false }] })

/-- The call `POST /eth/v1/remotekeys`: the status of each key, in order, and the state after. -/
def importRemoteKeys : KeyState → List ImportRemoteSignerDefinition → List ImportStatus × KeyState
  | state, [] => ([], state)
  | state, definition :: rest =>
    let (status, state) := importRemoteKey state definition
    let (statuses, state) := importRemoteKeys state rest
    (status :: statuses, state)

/-! ## Deleting -/

/-- The status of one remote key of a request to delete them, and the state after it. -/
def deleteRemoteKey (state : KeyState) (pubkey : BLSPubkey) : DeleteStatus × KeyState :=
  if state.remoteKeys.any (fun key => key.pubkey == pubkey && key.readonly == some true) then
    (.error "the key is read-only", state)
  else if state.remoteKeys.any (·.pubkey == pubkey) then
    (.deleted, { state with remoteKeys := state.remoteKeys.filter (·.pubkey != pubkey) })
  else (.notFound, state)

/-- The call `DELETE /eth/v1/remotekeys`: the status of each key, in order, and the state after. -/
def deleteRemoteKeys : KeyState → List BLSPubkey → List DeleteStatus × KeyState
  | state, [] => ([], state)
  | state, pubkey :: rest =>
    let (status, state) := deleteRemoteKey state pubkey
    let (statuses, state) := deleteRemoteKeys state rest
    (status :: statuses, state)

/-! ## The calls on their bodies -/

/-- The call `POST /eth/v1/remotekeys` on the body of a request, and the state after it. -/
def postRemoteKeys (state : KeyState) (body : Json) : Response × KeyState :=
  match readImportRemoteKeysRequest body with
  | .error _ => (badRequest "the request does not read", state)
  | .ok definitions =>
    let (statuses, state) := importRemoteKeys state definitions
    (⟨200, importResponseJson statuses⟩, state)

/-- The call `DELETE /eth/v1/remotekeys` on the body of a request, and the state after it.

Any body that reads gets HTTP 200, never 404. -/
def deleteRemoteKeysCall (state : KeyState) (body : Json) : Response × KeyState :=
  match readDeleteKeysRequest body with
  | .error _ => (badRequest "the request does not read", state)
  | .ok request =>
    let (statuses, state) := deleteRemoteKeys state request.pubkeys
    (⟨200, Json.mkObj [("data", .arr (statuses.map deleteStatusJson).toArray)]⟩, state)

end EthLib.Consensus.KeymanagerApi
