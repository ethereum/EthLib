module

public import EthLib.Consensus.KeymanagerApi.Client

/-!
# `Consensus.KeymanagerApi.DeleteKeys`

The calls of the Keymanager API that list the keys of a validator client and delete some of them.

They are `GET` and `DELETE` on `/eth/v1/keystores` of [`local_keystores.yaml`].

A delete follows the steps of the [flow].

It returns the data of the deleted and the not active keys, so that another client can import them.

The source says that a read-only key cannot be deleted from the API, and gives it no status.

Such a key here stays, with the status error, the only status that fits; `SOUNDNESS.md` notes it.

[`local_keystores.yaml`]: https://github.com/ethereum/keymanager-APIs/blob/2d8a02843cbf91f7ebc6274bf68a89b908019130/apis/local_keystores.yaml
[flow]: https://github.com/ethereum/keymanager-APIs/blob/2d8a02843cbf91f7ebc6274bf68a89b908019130/flows/README.md#delete
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
  -- The source: every key known to and decrypted by the client, here in the order of import.
  state.localKeys.map fun key =>
    -- The response schema: the public key is required, the path and the read-only flag optional.
    --
    -- EthLib always gives the flag, and leaves out an empty path.
    { validatingPubkey := key.pubkey
      derivationPath := if key.derivationPath.isEmpty then none else some key.derivationPath
      readonly := some key.readonly }

/-- A listed key as the API writes it. -/
def listedKeyJson (key : ListedKey) : Json :=
  -- The response schema: the public key, then the derivation path and the flag when set.
  Json.mkObj ([("validating_pubkey", Interchange.bytesJson key.validatingPubkey)] ++
    optionalFields "derivation_path" stringJson key.derivationPath ++
    optionalFields "readonly" Json.bool key.readonly)

/-- The body of the response that lists the keys, with HTTP 200. -/
def listKeysJson (keys : List ListedKey) : Json :=
  -- The response schema: the keys under data.
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
  -- The source: data only for a key whose status is deleted or not active.
  | .deleted | .notActive => true
  | _ => false

/-- The response to a request to delete keys. -/
structure DeleteKeysResponse where
  /-- The status of each key of the request, in order. -/
  data : List DeleteStatus
  /-- The data of the keys whose status is deleted or not active. -/
  slashingProtection : Interchange

/-- The status of one key before the record is read, and the state after it. -/
def deleteLocalKey (state : KeyState) (pubkey : BLSPubkey) : DeleteStatus × KeyState :=
  -- The source gives a read-only key no status; EthLib's choice is error, and the key stays.
  if state.isReadonly pubkey then (.error "the key is read-only", state)
  -- Flow, steps 2.1 and 2.5: a key the client holds stops signing, and is provisionally deleted.
  --
  -- EthLib's choice: steps 2.2 to 2.4 act on storage, which each client handles itself.
  else if state.isActive pubkey then
    (.deleted, { state with localKeys := state.localKeys.filter (·.pubkey != pubkey) })
  -- Flow, step 2.1: no matching key gives the provisional status not found.
  --
  -- A key named twice is deleted at its first place, and not held at its second.
  else (.notFound, state)

/-- The statuses of the keys before the record is read, in order, and the state after the last. -/
def deleteLocalKeys : KeyState → List BLSPubkey → List DeleteStatus × KeyState
  | state, [] => ([], state)
  -- Flow, step 2: each key of the request, one by one.
  | state, pubkey :: rest =>
    let (status, state) := deleteLocalKey state pubkey
    let (statuses, state) := deleteLocalKeys state rest
    (status :: statuses, state)

/-- The final status of a key: one not found that the record names is not active. -/
def finalStatus (record : Interchange) (pubkey : BLSPubkey) : DeleteStatus → DeleteStatus
  -- Flow, step 3: a key not found whose data the record holds is not active, else not found.
  | .notFound => if record.namesKey pubkey then .notActive else .notFound
  -- Flow, step 3: a deleted key stays deleted, whether or not the record holds its data.
  | status => status

/-- The keys of a request whose final status lets the response carry their data. -/
def exportedKeys (pubkeys : List BLSPubkey) (statuses : List DeleteStatus) : List BLSPubkey :=
  -- The source: the keys of the request whose status is deleted or not active.
  (pubkeys.zip statuses).filterMap fun (pubkey, status) =>
    if status.carriesData then some pubkey else none

/-- The call `DELETE /eth/v1/keystores`: the status of each key and its data, and the state.

The record of the client does not change, so a request sent again returns the same data. -/
def deleteKeys (state : KeyState) (request : DeleteKeysRequest) :
    DeleteKeysResponse × KeyState :=
  -- Flow, step 2: the provisional statuses, and the state without the deleted keys.
  let (provisional, after) := deleteLocalKeys state request.pubkeys
  -- Flow, step 3: the final statuses, read from the record of the client.
  --
  -- The record is a pure value, so its export cannot fail, unlike in the flow.
  let statuses := List.zipWith (finalStatus state.protection) request.pubkeys provisional
  -- Flow, step 4: the statuses in the order of the request, and the data of step 3.
  ({ data := statuses
     -- The source: never data of keys outside the request, and only for deleted or not active.
     slashingProtection := state.protection.entriesOf (exportedKeys request.pubkeys statuses) },
   -- The flow: the keymanager must never delete the slashing protection data of a key.
   after)

/-- The status of one key as the API writes it. -/
def deleteStatusJson : DeleteStatus → Json
  -- The response schema: deleted, not active, not found or error, with a message for an error.
  | .deleted => Json.mkObj [("status", "deleted")]
  | .notActive => Json.mkObj [("status", "not_active")]
  | .notFound => Json.mkObj [("status", "not_found")]
  | .error message => Json.mkObj [("status", "error"), ("message", .str message)]

/-- The body of the response to a delete, with HTTP 200, its data held as text. -/
def deleteKeysJson (text : JsonText) (response : DeleteKeysResponse) : Json :=
  -- The response schema: the statuses under data, and the EIP-3076 data as text.
  Json.mkObj [("data", .arr (response.data.map deleteStatusJson).toArray),
    ("slashing_protection", slashingProtectionJson text response.slashingProtection)]

/-- The call `DELETE /eth/v1/keystores` on the body of a request, and the state after it.

A body that does not read is refused with HTTP 400; any other gets HTTP 200, never 404. -/
def deleteKeystores (text : JsonText) (state : KeyState) (body : Json) : Response × KeyState :=
  match readDeleteKeysRequest body with
  -- Flow, step 1: a request that does not deserialize gets HTTP 400.
  | .error _ => (badRequest "the request does not read", state)
  | .ok request =>
    let (response, state) := deleteKeys state request
    -- Flow, step 1: after it, the response is HTTP 200; the source: it should never be 404.
    (⟨200, deleteKeysJson text response⟩, state)

end EthLib.Consensus.KeymanagerApi
