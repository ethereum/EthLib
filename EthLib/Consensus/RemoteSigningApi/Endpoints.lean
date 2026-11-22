module

public import EthLib.Consensus.RemoteSigningApi.SigningRoot
public import EthLib.Consensus.SlashingProtection
public import EthLib.Serialization.Ssz.Codec.HexBytes

/-!
# `Consensus.RemoteSigningApi.Endpoints`

The two endpoints of a remote signer: the list of its public keys, and the signing of a request.

The [public keys endpoint] lists the keys, and the [sign endpoint] signs a request or refuses it.

The source fixes the status codes of the sign endpoint, not the rules of slashing protection.

So the rules are a parameter, with one instance from EIP-3076, which records blocks and votes.

[public keys endpoint]: https://github.com/ethereum/remote-signing-api/blob/514525ca961a9d001e96a02bf870285a8ae401a4/signing/paths/public_keys.yaml
[sign endpoint]: https://github.com/ethereum/remote-signing-api/blob/514525ca961a9d001e96a02bf870285a8ae401a4/signing/paths/sign.yaml
-/

@[expose] public section

namespace EthLib.Consensus.RemoteSigningApi

open Lean Base Cryptography.Bls Serialization.Ssz

/-- The state of a remote signer: its secret keys and the record of its slashing protection.

The signer holds secret keys only, so each public key is the one of a held secret key. -/
structure SignerState where
  /-- The secret keys that have been loaded. -/
  keys : List Signatures.SecretKey
  /-- The record of the messages that the keys have signed. -/
  protection : Interchange

/-- The public keys of a signer, one for each secret key that it holds. -/
def publicKeys (state : SignerState) : List BLSPubkey :=
  -- The source: the public keys for the private keys that have been loaded.
  state.keys.map Signatures.skToPk

/-- The key that the path of a request names: 48 bytes as hex after `0x`, in either case. -/
def readIdentifier (identifier : String) : Option BLSPubkey :=
  -- The source: a BLS public key in hex format.
  --
  -- EthLib's reading: the `0x` prefix and 96 hex digits, so other spellings are refused.
  parseHexBytes 48 identifier

/-- A rule of slashing protection: it refuses a request of a key, or records it.

It sees the record, the key, the request and the root that the signer would sign. -/
abbrev SlashingPolicy (preset : Preset) : Type :=
  Interchange → BLSPubkey → SigningRequest preset → Root →
    Except SlashingProtectionError Interchange

/-- The slot of the block of a request of the second block kind. -/
def BlockV2Body.slot {preset : Preset} : BlockV2Body preset → Slot
  -- The slot of the whole block up to Altair, and of the header from Bellatrix.
  | .phase0 block | .altair block => block.slot
  | .header _ blockHeader => blockHeader.slot

/-- The rule of EIP-3076: a block or a vote is checked against the record, then recorded. -/
def eip3076Policy {preset : Preset} : SlashingPolicy preset := fun record pubkey request root =>
  match request with
  -- EIP-3076, conditions 1 and 2: refuse a block slashable with a recorded one.
  --
  -- Also refuse a slot at most the least recorded slot, unless it repeats a signing.
  | .block _ block => do
    record.checkBlock pubkey block.slot root
    -- Else the record takes its slot and signing root.
    return record.recordBlock pubkey block.slot root
  | .blockV2 _ body => do
    record.checkBlock pubkey body.slot root
    return record.recordBlock pubkey body.slot root
  -- EIP-3076, conditions 3 to 5: refuse a vote slashable with a recorded one.
  --
  -- Also refuse a source or a target epoch too low against the record, as the EIP sets.
  | .attestation _ data => do
    record.checkAttestation pubkey data.source.epoch data.target.epoch root
    -- Else the record takes its source epoch, its target epoch and its signing root.
    return record.recordAttestation pubkey data.source.epoch data.target.epoch root
  -- EIP-3076 records blocks and votes only, so every other kind passes, and nothing records it.
  | _ => .ok record

/-- What the sign endpoint answers. -/
inductive SignResult where
  /-- The signature of the root of the request, with status 200. -/
  | signed (signature : BLSSignature)
  /-- The document is not a request, with status 400; the error says why. -/
  | badRequest (error : RequestError)
  /-- The path names no key in hex, with status 400; the error gives the path. -/
  | badIdentifier (identifier : String)
  /-- The request carries a signing root other than the signer's, with status 400.

  The error gives the root of the request, then that of the signer. -/
  | rootMismatch (requestRoot signerRoot : Root)
  /-- The signer holds no secret key for the public key, with status 404. -/
  | unknownKey (pubkey : BLSPubkey)
  /-- Slashing protection refuses the request, with status 412; the error says why. -/
  | slashable (error : SlashingProtectionError)
  /-- The root of the request has no value, with status 500. -/
  | rootFailed (fault : Err)
  /-- The signature fails, with status 500. -/
  | signingFailed (error : BlsError)

/-- The HTTP status of a result, as the sign endpoint lists them. -/
def SignResult.status : SignResult → Nat
  -- The source: 200, the signature.
  | .signed _ => 200
  -- The source: 400, a bad request format.
  --
  -- EthLib's choice: a root that differs from the signer's is one too.
  | .badRequest _ | .badIdentifier _ | .rootMismatch .. => 400
  -- The source: 404, the public key is not found.
  | .unknownKey _ => 404
  -- The source: 412, the signing operation failed due to slashing protection rules.
  | .slashable _ => 412
  -- The source: 500, an internal server error.
  | .rootFailed _ | .signingFailed _ => 500

/-- The signing root that a request carries, if the client sends one. -/
def SigningRequest.signingRoot? {preset : Preset} : SigningRequest preset → Option Root
  | .aggregationSlot signing _ | .aggregateAndProof signing _ | .aggregateAndProofV2 signing _ _
  | .attestation signing _ | .block signing _ | .blockV2 signing _ | .randaoReveal signing _
  | .voluntaryExit signing _ | .syncCommitteeMessage signing _
  | .syncCommitteeSelectionProof signing _ | .syncCommitteeContributionAndProof signing _
  | .executionPayloadBid signing _ | .executionPayloadEnvelope signing _
  | .payloadAttestationMessage signing _ | .proposerPreferences signing _ => signing.signingRoot
  | .deposit signingRoot _ | .validatorRegistration signingRoot _
  | .builderRequestAuth signingRoot _ _ => signingRoot

/-- The last step of the sign endpoint: slashing protection, then the signature of the root.

The state changes only when both pass. -/
def protectAndSign {preset : Preset} (protect : SlashingPolicy preset) (state : SignerState)
    (pubkey : BLSPubkey) (key : Signatures.SecretKey) (request : SigningRequest preset)
    (root : Root) : SignResult × SignerState :=
  -- Slashing protection first: a refusal is HTTP 412.
  match protect state.protection pubkey request root with
  | .error error => (.slashable error, state)
  | .ok protection =>
    -- The BLS signature of the signing root under the secret key.
    match Signatures.sign key (packBytes root) with
    | .error error => (.signingFailed error, state)
    -- The record takes the request only with the signature.
    | .ok signature => (.signed signature, { state with protection })

/-- The answer of the sign endpoint to a document for the key that a path names, and the state.

Only a signature changes the state. -/
def sign (preset : Preset) (config : Config) (protect : SlashingPolicy preset)
    (state : SignerState) (identifier : String) (document : Json) : SignResult × SignerState :=
  -- The request body, one of the schemas that its type names, else HTTP 400.
  match SigningRequest.ofJson preset document with
  | .error error => (.badRequest error, state)
  | .ok request =>
    -- The identifier of the path, a public key, else HTTP 400.
    match readIdentifier identifier with
    | none => (.badIdentifier identifier, state)
    | some pubkey =>
      -- The source: a public key with no loaded private key gets HTTP 404.
      match state.keys.find? (Signatures.skToPk · = pubkey) with
      | none => (.unknownKey pubkey, state)
      | some key =>
        -- The signing root of the request, computed by the signer.
        match requestSigningRoot config request with
        | .error fault => (.rootFailed fault, state)
        | .ok root =>
          -- The schemas: a signing root sent by the client is for optional verification.
          --
          -- EthLib verifies it, and refuses one other than the signer's.
          match request.signingRoot?.filter (· != root) with
          | some requestRoot => (.rootMismatch requestRoot root, state)
          -- Then slashing protection and the signature.
          | none => protectAndSign protect state pubkey key request root

/-! ## What a run of calls signs -/

/-- The slot of a request of a block kind, if it is one. -/
def SigningRequest.blockSlot? {preset : Preset} : SigningRequest preset → Option Slot
  | .block _ beaconBlock => some beaconBlock.slot
  | .blockV2 _ body => some body.slot
  | _ => none

/-- The data of a request of the attestation kind, if it is one. -/
def SigningRequest.attestationData? {preset : Preset} :
    SigningRequest preset → Option AttestationData
  | .attestation _ data => some data
  | _ => none

/-- The key, the slot and the root of a block that a call names, if it names one. -/
def blockOfCall? (preset : Preset) (config : Config) (identifier : String) (document : Json) :
    Option (BLSPubkey × Slot × Root) := do
  -- The request, the key of the path, the slot of a block kind and the signing root.
  let request ← (SigningRequest.ofJson preset document).toOption
  let pubkey ← readIdentifier identifier
  let slot ← request.blockSlot?
  let root ← (requestSigningRoot config request).toOption
  return (pubkey, slot, root)

/-- The key, the data and the root of a vote that a call names, if it names one. -/
def voteOfCall? (preset : Preset) (config : Config) (identifier : String) (document : Json) :
    Option (BLSPubkey × AttestationData × Root) := do
  -- The request, the key of the path, the data of an attestation and the signing root.
  let request ← (SigningRequest.ofJson preset document).toOption
  let pubkey ← readIdentifier identifier
  let data ← request.attestationData?
  let root ← (requestSigningRoot config request).toOption
  return (pubkey, data, root)

/-- The blocks that a run of calls signs under the rule of EIP-3076, in order. -/
def signedBlocks (preset : Preset) (config : Config) :
    SignerState → List (String × Json) → List (BLSPubkey × Slot × Root)
  | _, [] => []
  | state, (identifier, document) :: rest =>
    -- Each call in turn, on the state that the call before it left.
    let (result, next) := sign preset config eip3076Policy state identifier document
    -- A call that gives a signature and names a block adds that block.
    let signed := match result with
      | .signed _ => (blockOfCall? preset config identifier document).toList
      | _ => []
    signed ++ signedBlocks preset config next rest

/-- The votes that a run of calls signs under the rule of EIP-3076, in order. -/
def signedVotes (preset : Preset) (config : Config) :
    SignerState → List (String × Json) → List (BLSPubkey × AttestationData × Root)
  | _, [] => []
  | state, (identifier, document) :: rest =>
    -- Each call in turn, on the state that the call before it left.
    let (result, next) := sign preset config eip3076Policy state identifier document
    -- A call that gives a signature and names a vote adds that vote.
    let signed := match result with
      | .signed _ => (voteOfCall? preset config identifier document).toList
      | _ => []
    signed ++ signedVotes preset config next rest

end EthLib.Consensus.RemoteSigningApi
