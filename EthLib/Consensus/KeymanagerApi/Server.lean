module

public import EthLib.Consensus.KeymanagerApi.DeleteKeys
public import EthLib.Consensus.KeymanagerApi.LocalKeys
public import EthLib.Consensus.KeymanagerApi.RemoteKeys

/-!
# `Consensus.KeymanagerApi.Server`

The call of the Keymanager API that a method and a path name, on the state of a validator client.

The paths are those of the [OpenAPI document], split into their segments.

Every other method and path gets HTTP 404, including calls that this module does not model yet.

[OpenAPI document]: https://github.com/ethereum/keymanager-APIs/blob/51f2a5c90e9d301c3e9980da402ec70ae82f0991/keymanager-oapi.yaml
-/

@[expose] public section

namespace EthLib.Consensus.KeymanagerApi

open Lean

/-- The segments of a path, between its slashes, with empty segments left out. -/
def pathSegments (path : String) : List String :=
  (path.splitOn "/").filter (· ≠ "")

/-- The response with HTTP 404 for a path that is not served. -/
def notFound : Response :=
  ⟨404, errorResponseJson ⟨"Path not found"⟩⟩

/-- The response of the call that a method and a path name, and the state after it. -/
def handle (text : JsonText) (config : ClientConfig) (state : KeyState) (method path : String)
    (body : Json) : Response × KeyState :=
  match method, pathSegments path with
  | "GET", ["eth", "v1", "keystores"] => getKeystores state
  | "POST", ["eth", "v1", "keystores"] => postKeystores text config.limits state body
  | "DELETE", ["eth", "v1", "keystores"] => deleteKeystores text state body
  | "GET", ["eth", "v1", "remotekeys"] => getRemoteKeys state
  | "POST", ["eth", "v1", "remotekeys"] => postRemoteKeys state body
  | "DELETE", ["eth", "v1", "remotekeys"] => deleteRemoteKeysCall state body
  | _, _ => (notFound, state)

end EthLib.Consensus.KeymanagerApi
