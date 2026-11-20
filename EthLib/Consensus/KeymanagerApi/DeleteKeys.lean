module

public import EthLib.Consensus.KeymanagerApi.Client

/-!
# `Consensus.KeymanagerApi.DeleteKeys`

The calls of the Keymanager API that list the keys of a validator client and delete some of them.

They are `GET` and `DELETE` on `/eth/v1/keystores` of [`local_keystores.yaml`].

The list gives every key that the client holds, in order.

A delete removes each key of the request that the client holds, and stops it signing.

It returns the slashing protection data of those keys, so that another client can import them.

The record of the client keeps that data: "The keymanager must never delete" it, by the [flow].

A key that the client no longer holds at its turn, but that its record names, is not active.

A key that the client no longer holds and that its record does not name is not found.

So a key named twice is deleted at its first place, and not active at its second.

Only the data of keys with the status deleted or not active is returned.

The source says that a read-only key "cannot be deleted from the API", and gives it no status.

Such a key here stays, with the status error, the only status that fits; `SOUNDNESS.md` notes it.

A record of EIP-3076 is a pure value here, so its export cannot fail, unlike in the flow.

[`local_keystores.yaml`]: https://github.com/ethereum/keymanager-APIs/blob/51f2a5c90e9d301c3e9980da402ec70ae82f0991/apis/local_keystores.yaml
[flow]: https://github.com/ethereum/keymanager-APIs/blob/51f2a5c90e9d301c3e9980da402ec70ae82f0991/flows/README.md#delete
-/

@[expose] public section

namespace EthLib.Consensus.KeymanagerApi

open Lean Base Cryptography.Bls

/-! ## Listing the keys -/

/-- A key as the call that lists keys gives it. -/
structure ListedKey where
  /-- The public key. -/
  validatingPubkey : BLSPubkey
  /-- The derivation path of the keystore, if it named one. -/
  derivationPath : Option String
  /-- Whether the key cannot be deleted through the API. -/
  readonly : Option Bool
  deriving DecidableEq, Repr

/-- The call `GET /eth/v1/keystores`: every key that the client holds, in order.

An empty derivation path is left out, since the keystore then names none. -/
def listKeys (state : KeyState) : List ListedKey :=
  state.localKeys.map fun key =>
    { validatingPubkey := key.pubkey
      derivationPath := if key.derivationPath.isEmpty then none else some key.derivationPath
      readonly := some key.readonly }

/-- A listed key as the API writes it. -/
def listedKeyJson (key : ListedKey) : Json :=
  Json.mkObj ([("validating_pubkey", Interchange.bytesJson key.validatingPubkey)] ++
    optionalFields "derivation_path" stringJson key.derivationPath ++
    optionalFields "readonly" Json.bool key.readonly)

/-- The body of the response that lists the keys, with HTTP 200. -/
def listKeysJson (keys : List ListedKey) : Json :=
  Json.mkObj [("data", .arr (keys.map listedKeyJson).toArray)]

/-- The call `GET /eth/v1/keystores`, with HTTP 200, which leaves the state as it was. -/
def getKeystores (state : KeyState) : Response × KeyState :=
  (⟨200, listKeysJson (listKeys state)⟩, state)

/-! ## Deleting keys -/

/-- The status of one key of a request to delete keys. -/
inductive DeleteStatus where
  /-- The client held the key, and no longer does. -/
  | deleted
  /-- The client no longer held the key at its turn, and its record names it. -/
  | notActive
  /-- The client no longer held the key at its turn, and its record does not name it. -/
  | notFound
  /-- The key could not be deleted, for the reason given. -/
  | error (message : String)
  deriving DecidableEq, Repr

/-- Whether a status lets the response carry the slashing protection data of its key. -/
def DeleteStatus.carriesData : DeleteStatus → Bool
  | .deleted | .notActive => true
  | _ => false

/-- The response to a request to delete keys. -/
structure DeleteKeysResponse where
  /-- The status of each key of the request, in order. -/
  data : List DeleteStatus
  /-- The data of the keys whose status is deleted or not active. -/
  slashingProtection : Interchange

/-- The status of one key before the record is read, and the state after it.

A key that the client holds read-only stays, with an error status. -/
def deleteLocalKey (state : KeyState) (pubkey : BLSPubkey) : DeleteStatus × KeyState :=
  if state.isReadonly pubkey then (.error "the key is read-only", state)
  else if state.isActive pubkey then
    (.deleted, { state with localKeys := state.localKeys.filter (·.pubkey != pubkey) })
  else (.notFound, state)

/-- The statuses of the keys before the record is read, in order, and the state after the last. -/
def deleteLocalKeys : KeyState → List BLSPubkey → List DeleteStatus × KeyState
  | state, [] => ([], state)
  | state, pubkey :: rest =>
    let (status, state) := deleteLocalKey state pubkey
    let (statuses, state) := deleteLocalKeys state rest
    (status :: statuses, state)

/-- The final status of a key: one not found that the record names is not active. -/
def finalStatus (record : Interchange) (pubkey : BLSPubkey) : DeleteStatus → DeleteStatus
  | .notFound => if record.namesKey pubkey then .notActive else .notFound
  | status => status

/-- The keys of a request whose final status lets the response carry their data. -/
def exportedKeys (pubkeys : List BLSPubkey) (statuses : List DeleteStatus) : List BLSPubkey :=
  (pubkeys.zip statuses).filterMap fun (pubkey, status) =>
    if status.carriesData then some pubkey else none

/-- The call `DELETE /eth/v1/keystores`: the status of each key and its data, and the state.

The record of the client does not change, so a request sent again returns the same data. -/
def deleteKeys (state : KeyState) (request : DeleteKeysRequest) :
    DeleteKeysResponse × KeyState :=
  let (provisional, after) := deleteLocalKeys state request.pubkeys
  let statuses := List.zipWith (finalStatus state.protection) request.pubkeys provisional
  ({ data := statuses
     slashingProtection := state.protection.entriesOf (exportedKeys request.pubkeys statuses) },
   after)

/-- The status of one key as the API writes it. -/
def deleteStatusJson : DeleteStatus → Json
  | .deleted => Json.mkObj [("status", "deleted")]
  | .notActive => Json.mkObj [("status", "not_active")]
  | .notFound => Json.mkObj [("status", "not_found")]
  | .error message => Json.mkObj [("status", "error"), ("message", .str message)]

/-- The body of the response to a delete, with HTTP 200, its data held as text. -/
def deleteKeysJson (text : JsonText) (response : DeleteKeysResponse) : Json :=
  Json.mkObj [("data", .arr (response.data.map deleteStatusJson).toArray),
    ("slashing_protection", slashingProtectionJson text response.slashingProtection)]

/-- The call `DELETE /eth/v1/keystores` on the body of a request, and the state after it.

A body that does not read is refused with HTTP 400; any other gets HTTP 200, never 404. -/
def deleteKeystores (text : JsonText) (state : KeyState) (body : Json) : Response × KeyState :=
  match readDeleteKeysRequest body with
  | .error _ => (badRequest "the request does not read", state)
  | .ok request =>
    let (response, state) := deleteKeys state request
    (⟨200, deleteKeysJson text response⟩, state)

end EthLib.Consensus.KeymanagerApi
