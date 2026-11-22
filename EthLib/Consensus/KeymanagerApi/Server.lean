module

public import EthLib.Consensus.KeymanagerApi.DeleteKeys
public import EthLib.Consensus.KeymanagerApi.LocalKeys
public import EthLib.Consensus.KeymanagerApi.RemoteKeys
public import EthLib.Consensus.KeymanagerApi.Settings
public import EthLib.Consensus.KeymanagerApi.VoluntaryExit

/-!
# `Consensus.KeymanagerApi.Server`

The call of the Keymanager API that a method and a path name, on the state of a validator client.

The paths are those of the [OpenAPI document], split into their segments, and may have a query.

A view of the chain, if the client has one, serves the call that signs a voluntary exit.

Every other method and path gets HTTP 404, including calls that this module does not model yet.

[OpenAPI document]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/keymanager-oapi.yaml
-/

@[expose] public section

namespace EthLib.Consensus.KeymanagerApi

open Lean

/-- The segments of a path, between its slashes, with empty segments left out. -/
def pathSegments (path : String) : List String :=
  (path.splitOn "/").filter (· ≠ "")

/-- The response with HTTP 404 for a path that is not served. -/
def notFound : Response :=
  -- EthLib's choice: the source lists no response for a path that it does not define.
  ⟨404, errorResponseJson ⟨"Path not found"⟩⟩

/-- A call on the key that a segment of a path names; a segment that is no key gets HTTP 400. -/
def withPubkey (segment : String) (state : KeyState)
    (call : Cryptography.Bls.BLSPubkey → Response × KeyState) : Response × KeyState :=
  -- The source: the path parameter is a public key, 48 bytes of hex after 0x.
  match readPubkey "pubkey" (.str segment) with
  | .ok pubkey => call pubkey
  -- The source: a malformed request gets HTTP 400.
  | .error _ => (badRequest "the public key of the path does not read", state)

/-- The response of the call that a method and a path name, and the state after it. -/
def handle (text : JsonText) (config : ClientConfig) (chain : Option ChainView) (state : KeyState)
    (method path : String) (body : Json) : Response × KeyState :=
  -- The path before the first question mark, and the query after it.
  let route := (path.splitOn "?").headD ""
  let query := ((path.splitOn "?").drop 1).headD ""
  match method, pathSegments route with
  -- The paths of the OpenAPI document, each with its methods.
  | "GET", ["eth", "v1", "keystores"] => getKeystores state
  | "POST", ["eth", "v1", "keystores"] => postKeystores text config.limits state body
  | "DELETE", ["eth", "v1", "keystores"] => deleteKeystores text state body
  | "GET", ["eth", "v1", "remotekeys"] => getRemoteKeys state
  | "POST", ["eth", "v1", "remotekeys"] => postRemoteKeys state body
  | "DELETE", ["eth", "v1", "remotekeys"] => deleteRemoteKeysCall state body
  | method, ["eth", "v1", "validator", key, "feerecipient"] =>
    withPubkey key state fun pubkey => feeRecipientCalls.handle config state method pubkey body
  | method, ["eth", "v1", "validator", key, "gas_limit"] =>
    withPubkey key state fun pubkey => gasLimitCalls.handle config state method pubkey body
  | method, ["eth", "v1", "validator", key, "graffiti"] =>
    withPubkey key state fun pubkey => graffitiCalls.handle config state method pubkey body
  | method, ["eth", "v1", "validator", key, "builder_config"] =>
    withPubkey key state fun pubkey => builderConfigCalls.handle config state method pubkey body
  | "POST", ["eth", "v1", "validator", key, "voluntary_exit"] =>
    withPubkey key state fun pubkey => (postVoluntaryExit chain state pubkey query, state)
  | _, _ => (notFound, state)

end EthLib.Consensus.KeymanagerApi
