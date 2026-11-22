module

public import EthLib.Consensus.KeymanagerApi.Client
public import EthLib.Consensus.Transition.Operations
public import EthLib.Consensus.Transition.SyncAggregate

/-!
# `Consensus.KeymanagerApi.VoluntaryExit`

The call of the Keymanager API that signs a voluntary exit with a key of a validator client.

It is `POST /eth/v1/validator/{pubkey}/voluntary_exit` of [`voluntary_exit.yaml`].

The chain is the state that the client reads from its beacon node.

From Deneb the domain of an exit is fixed on the Capella fork version, by [EIP-7044].

The source does not say which of its codes applies to a validator not in the state, or not active.

This call does not check that the validator is active; the chain does when it processes the exit.

[`voluntary_exit.yaml`]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/apis/voluntary_exit.yaml
[EIP-7044]: https://eips.ethereum.org/EIPS/eip-7044#specification
-/

@[expose] public section

namespace EthLib.Consensus.KeymanagerApi

open Lean Base Cryptography.Bls

variable {preset : Preset} {fork : Fork}

/-- Why a voluntary exit is not signed. -/
inductive ExitError where
  /-- The client does not hold the key. -/
  | unknownKey
  /-- No validator of the state has the key. -/
  | notValidator
  /-- The domain or the signing root does not compute, or the signature fails. -/
  | signing
  deriving DecidableEq, Repr

/-- The key that the client holds under a public key, if any. -/
def KeyState.localKey? (state : KeyState) (pubkey : BLSPubkey) : Option LocalKey :=
  state.localKeys.find? (·.pubkey == pubkey)

/-- The call `POST /eth/v1/validator/{pubkey}/voluntary_exit`: the signed exit of a key.

The epoch is the one given, or the current epoch of the state. -/
def signVoluntaryExit (config : Config) (state : BeaconState preset fork) (keys : KeyState)
    (pubkey : BLSPubkey) (epoch : Option Epoch) : Except ExitError SignedVoluntaryExit := do
  -- The source: the path names an active validator known to the validator client.
  let some key := keys.localKey? pubkey | throw .unknownKey
  -- The index of the exiting validator: the first position of the key in the registry of the state.
  let .ok validatorIndex := validatorIndexOfPubkey state pubkey | throw .notValidator
  -- The source: the epoch is the minimum epoch for processing the exit.
  --
  -- It defaults to the current epoch if not set.
  let message : VoluntaryExit := { epoch := epoch.getD (getCurrentEpoch state), validatorIndex }
  -- The domain of a voluntary exit at that epoch in the state, as EIP-7044 fixes it from Deneb.
  let .ok domain := voluntaryExitDomain config state message.epoch | throw .signing
  -- The signing root: the root of the signing data, made of the root of the exit and the domain.
  let .ok root := computeSigningRoot message domain | throw .signing
  -- The BLS signature of the signing root under the secret key.
  let .ok signature := Signatures.sign key.secretKey (packBytes root) | throw .signing
  -- The source: the signed voluntary exit, the exit with its signature.
  return { message, signature }

/-! ## The call on its path -/

/-- The view of the chain that a client reads from its beacon node: a state with its settings. -/
structure ChainView where
  /-- The preset of the chain. -/
  preset : Preset
  /-- The fork of the state. -/
  fork : Fork
  /-- The configuration of the chain. -/
  config : Config
  /-- The state. -/
  state : BeaconState preset fork

/-- The epoch of the query of a path, if it gives one, or why it does not read. -/
def queryEpoch (query : String) : Except KeymanagerError (Option Epoch) :=
  -- The source: an optional query parameter epoch, a 64-bit integer in decimal digits.
  --
  -- EthLib's choice: the first pair named epoch counts.
  match (query.splitOn "&").find? (·.startsWith "epoch=") with
  | some pair => some <$> readUint64 "epoch" (.str (pair.drop 6).toString)
  | none => .ok none

/-- The call `POST /eth/v1/validator/{pubkey}/voluntary_exit`, with its query, and its response.

A key that the client does not hold gets HTTP 404 before the chain or the query is read.

The state of the client does not change. -/
def postVoluntaryExit (chain : Option ChainView) (keys : KeyState) (pubkey : BLSPubkey)
    (query : String) : Response :=
  -- The source: HTTP 404 means that the key was not found on the server.
  if (keys.localKey? pubkey).isNone then
    ⟨404, errorResponseJson ⟨"The key was not found on the server"⟩⟩ else
  match chain with
  -- EthLib's choice: a client with no view of the chain cannot sign, an internal error.
  | none => ⟨500, errorResponseJson ⟨"the client has no view of the chain"⟩⟩
  | some view =>
    match queryEpoch query with
    -- The source: a malformed request gets HTTP 400.
    | .error _ => badRequest "the epoch of the query does not read"
    | .ok epoch =>
      match signVoluntaryExit view.config view.state keys pubkey epoch with
      | .error .unknownKey => ⟨404, errorResponseJson ⟨"The key was not found on the server"⟩⟩
      -- EthLib's choice: a key with no validator in the state gets HTTP 400.
      | .error .notValidator => badRequest "no validator of the chain has the key"
      | .error .signing => ⟨500, errorResponseJson ⟨"the exit could not be signed"⟩⟩
      | .ok signed =>
        match signedVoluntaryExitJson signed with
        -- The source: HTTP 200, with the signed voluntary exit under data.
        | .ok document => ⟨200, Json.mkObj [("data", document)]⟩
        | .error _ => ⟨500, errorResponseJson ⟨"the exit could not be written"⟩⟩

end EthLib.Consensus.KeymanagerApi
