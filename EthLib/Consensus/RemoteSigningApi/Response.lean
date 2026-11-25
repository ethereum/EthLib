module

public import EthLib.Consensus.BeaconApi.Spelling

/-!
# `Consensus.RemoteSigningApi.Response`

The responses of a remote signer: a signature, and the list of its public keys.

The [sign endpoint] answers with the signature as JSON under `signature`, or as plain hex.

The [public keys endpoint] answers with a JSON array of keys as hex.

[sign endpoint]: https://github.com/ethereum/remote-signing-api/blob/514525ca961a9d001e96a02bf870285a8ae401a4/signing/paths/sign.yaml
[public keys endpoint]: https://github.com/ethereum/remote-signing-api/blob/514525ca961a9d001e96a02bf870285a8ae401a4/signing/paths/public_keys.yaml
-/

@[expose] public section

namespace EthLib.Consensus.RemoteSigningApi

open Lean Base Serialization.Ssz BeaconApi Cryptography.Bls

/-- The JSON response to a request to sign, as the schema `SigningResponse` gives it. -/
structure SigningResponse where
  /-- The BLS signature. -/
  signature : BLSSignature
  deriving DecidableEq, Repr

instance : SszType SigningResponse :=
  .container ["signature"] (fun r => r.signature) (fun signature => ⟨signature⟩)

instance : ApiSpelling SigningResponse := .unmarked

/-- The plain-text response to a request to sign: the signature as hex alone. -/
def SigningResponse.text (response : SigningResponse) : String :=
  -- The source: the text/plain form is the signature as hex; its example writes 0x first.
  toHex ⟨response.signature.toArray⟩

/-- A public key is written as hex. -/
instance : ApiSpelling BLSPubkey := .unmarked

/-- The JSON response that lists the public keys of the signer. -/
def publicKeysJson (keys : List BLSPubkey) : Except Err Json := do
  -- The source: an array of strings, each a public key as hex.
  return .arr (← keys.mapM toApiJson).toArray

/-- The public keys that a JSON response lists, each 48 bytes as hex. -/
def readPublicKeys (document : Json) : Except Err (List BLSPubkey) :=
  match document with
  -- The source: an array of strings; EthLib's reading: each is a key of 48 bytes.
  | .arr entries => entries.toList.mapM (ofApiJson BLSPubkey)
  | _ => .error .typeMismatch

end EthLib.Consensus.RemoteSigningApi
