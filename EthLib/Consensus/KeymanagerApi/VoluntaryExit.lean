module

public import EthLib.Consensus.KeymanagerApi.Client
public import EthLib.Consensus.Transition.Operations
public import EthLib.Consensus.Transition.SyncAggregate

/-!
# `Consensus.KeymanagerApi.VoluntaryExit`

The call of the Keymanager API that signs a voluntary exit with a key of a validator client.

It is `POST /eth/v1/validator/{pubkey}/voluntary_exit` of [`voluntary_exit.yaml`].

The path names the key of "an active validator known to the validator client".

The query may give the epoch of the exit, the "Minimum epoch for processing exit".

Without it, the epoch is the current epoch of the chain.

The chain is the state that the client reads from its beacon node.

The signature uses the domain of a voluntary exit in that state.

From Deneb that domain is fixed on the Capella fork version, by [EIP-7044].

A key that the client does not hold gets HTTP 404, and one with no validator in the state HTTP 400.

The source does not say which of its codes applies to a validator not in the state, or not active.

This call does not check that the validator is active; the chain does when it processes the exit.

[`voluntary_exit.yaml`]: https://github.com/ethereum/keymanager-APIs/blob/51f2a5c90e9d301c3e9980da402ec70ae82f0991/apis/voluntary_exit.yaml
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
  let some key := keys.localKey? pubkey | throw .unknownKey
  let .ok validatorIndex := validatorIndexOfPubkey state pubkey | throw .notValidator
  let message : VoluntaryExit := { epoch := epoch.getD (getCurrentEpoch state), validatorIndex }
  let .ok domain := voluntaryExitDomain config state message.epoch | throw .signing
  let .ok root := computeSigningRoot message domain | throw .signing
  let .ok signature := Signatures.sign key.secretKey (packBytes root) | throw .signing
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
  match (query.splitOn "&").find? (·.startsWith "epoch=") with
  | some pair => some <$> readUint64 "epoch" (.str (pair.drop 6).toString)
  | none => .ok none

/-- The call `POST /eth/v1/validator/{pubkey}/voluntary_exit`, with its query, and its response.

A key that the client does not hold gets HTTP 404 before the chain or the query is read.

The state of the client does not change. -/
def postVoluntaryExit (chain : Option ChainView) (keys : KeyState) (pubkey : BLSPubkey)
    (query : String) : Response :=
  if (keys.localKey? pubkey).isNone then
    ⟨404, errorResponseJson ⟨"The key was not found on the server"⟩⟩ else
  match chain with
  | none => ⟨500, errorResponseJson ⟨"the client has no view of the chain"⟩⟩
  | some view =>
    match queryEpoch query with
    | .error _ => badRequest "the epoch of the query does not read"
    | .ok epoch =>
      match signVoluntaryExit view.config view.state keys pubkey epoch with
      | .error .unknownKey => ⟨404, errorResponseJson ⟨"The key was not found on the server"⟩⟩
      | .error .notValidator => badRequest "no validator of the chain has the key"
      | .error .signing => ⟨500, errorResponseJson ⟨"the exit could not be signed"⟩⟩
      | .ok signed =>
        match signedVoluntaryExitJson signed with
        | .ok document => ⟨200, Json.mkObj [("data", document)]⟩
        | .error _ => ⟨500, errorResponseJson ⟨"the exit could not be written"⟩⟩

end EthLib.Consensus.KeymanagerApi
