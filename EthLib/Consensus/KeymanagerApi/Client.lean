module

public import EthLib.Consensus.KeymanagerApi.Types
public import EthLib.Cryptography.Keystore

/-!
# `Consensus.KeymanagerApi.Client`

The state of a validator client that the calls of the Keymanager API read and change.

It holds the keys that the client signs with, and its slashing protection record by EIP-3076.

Storage, crash safety and the server machinery of the API are left to each client.

The settings that a client fixes at its start, such as the bounds of key derivation, are a value.
-/

@[expose] public section

namespace EthLib.Consensus.KeymanagerApi

open Lean Base Cryptography Cryptography.Bls

/-! ## The keys of a validator client -/

/-- A key that the validator client holds and signs with. -/
structure LocalKey where
  /-- The public key; an import derives it from the secret key. -/
  pubkey : BLSPubkey
  /-- The secret key. -/
  secretKey : Signatures.SecretKey
  /-- The derivation path that the keystore names, which may be empty. -/
  derivationPath : String
  /-- Whether the key cannot be deleted through the API. -/
  readonly : Bool

/-- The keys of a validator client and its slashing protection record. -/
structure KeyState where
  /-- The keys that the client holds, in the order they were imported. -/
  localKeys : List LocalKey
  /-- The keys that the client signs with through a remote signer. -/
  remoteKeys : List SignerDefinition
  /-- The record of what the keys signed, by EIP-3076. -/
  protection : Interchange
  /-- The fee recipient set for each key, latest first. -/
  feeRecipients : List (BLSPubkey × ExecutionAddress) := []
  /-- The gas limit set for each key, latest first. -/
  gasLimits : List (BLSPubkey × UInt64) := []
  /-- The graffiti set for each key, latest first. -/
  graffiti : List (BLSPubkey × String) := []

/-- Whether a key is active: the client holds it. -/
def KeyState.isActive (state : KeyState) (pubkey : BLSPubkey) : Bool :=
  state.localKeys.any (·.pubkey == pubkey)

/-- Whether the client holds a key that cannot be deleted through the API. -/
def KeyState.isReadonly (state : KeyState) (pubkey : BLSPubkey) : Bool :=
  state.localKeys.any fun key => key.pubkey == pubkey && key.readonly

/-- The settings that a validator client fixes at its start, which the source leaves to it. -/
structure ClientConfig where
  /-- The bounds on the key derivation of a keystore, which the source does not set. -/
  limits : Keystore.KdfLimits
  /-- The fee recipient of a key with none set. -/
  defaultFeeRecipient : ExecutionAddress
  /-- The gas limit of a key with none set. -/
  defaultGasLimit : UInt64
  /-- The graffiti of a key with none set. -/
  defaultGraffiti : String

end EthLib.Consensus.KeymanagerApi
