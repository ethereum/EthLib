module

public import EthLib.Consensus.RemoteSigningApi.SigningRoot
public import EthLib.Consensus.SlashingProtection

/-!
# `Consensus.RemoteSigningApi.Endpoints`

The two endpoints of a remote signer: the list of its public keys, and the signing of a request.

The [public keys endpoint] lists the keys "for the private keys that have been loaded".

The [sign endpoint] signs a request for the key that the path names, or refuses it.

It answers 400 for a request it cannot read, and 404 for an unknown key.

It answers 412 when slashing protection refuses the request.

The source fixes these status codes, not the rules of slashing protection.

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
  state.keys.map Signatures.skToPk

/-- The key that the path of a request names: 48 bytes as hex after `0x`, in either case.

The source says only "BLS public key in hex format", so other spellings are refused. -/
def readIdentifier (identifier : String) : Option BLSPubkey :=
  match ofHex identifier with
  | .ok data => exactBytes? 48 ⟨data⟩
  | .error _ => none

/-- A rule of slashing protection: it refuses a request of a key, or records it.

It sees the record, the key, the request and the root that the signer would sign. -/
abbrev SlashingPolicy (preset : Preset) : Type :=
  Interchange → BLSPubkey → SigningRequest preset → Root →
    Except SlashingProtectionError Interchange

/-- The slot of the block of a request of the second block kind. -/
def BlockV2Body.slot {preset : Preset} : BlockV2Body preset → Slot
  | .phase0 block | .altair block => block.slot
  | .header _ blockHeader => blockHeader.slot

/-- The rule of EIP-3076: a block or a vote is checked against the record, then recorded.

Every other kind of request passes, and nothing records it. -/
def eip3076Policy {preset : Preset} : SlashingPolicy preset := fun record pubkey request root =>
  match request with
  | .block _ block => do
    record.checkBlock pubkey block.slot root
    return record.recordBlock pubkey block.slot root
  | .blockV2 _ body => do
    record.checkBlock pubkey body.slot root
    return record.recordBlock pubkey body.slot root
  | .attestation _ data => do
    record.checkAttestation pubkey data.source.epoch data.target.epoch root
    return record.recordAttestation pubkey data.source.epoch data.target.epoch root
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
  | .signed _ => 200
  | .badRequest _ | .badIdentifier _ | .rootMismatch .. => 400
  | .unknownKey _ => 404
  | .slashable _ => 412
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
  match protect state.protection pubkey request root with
  | .error error => (.slashable error, state)
  | .ok protection =>
    match Signatures.sign key (packBytes root) with
    | .error error => (.signingFailed error, state)
    | .ok signature => (.signed signature, { state with protection })

/-- The answer of the sign endpoint to a document for the key that a path names, and the state.

It reads the request, then the key, then finds the secret key of that public key.

It computes the root, and refuses a request that carries another root.

It then asks slashing protection, and signs.

Only a signature changes the state. -/
def sign (preset : Preset) (config : Config) (protect : SlashingPolicy preset)
    (state : SignerState) (identifier : String) (document : Json) : SignResult × SignerState :=
  match SigningRequest.ofJson preset document with
  | .error error => (.badRequest error, state)
  | .ok request =>
    match readIdentifier identifier with
    | none => (.badIdentifier identifier, state)
    | some pubkey =>
      match state.keys.find? (Signatures.skToPk · = pubkey) with
      | none => (.unknownKey pubkey, state)
      | some key =>
        match requestSigningRoot config request with
        | .error fault => (.rootFailed fault, state)
        | .ok root =>
          match request.signingRoot?.filter (· != root) with
          | some requestRoot => (.rootMismatch requestRoot root, state)
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
  let request ← (SigningRequest.ofJson preset document).toOption
  let pubkey ← readIdentifier identifier
  let slot ← request.blockSlot?
  let root ← (requestSigningRoot config request).toOption
  return (pubkey, slot, root)

/-- The key, the data and the root of a vote that a call names, if it names one. -/
def voteOfCall? (preset : Preset) (config : Config) (identifier : String) (document : Json) :
    Option (BLSPubkey × AttestationData × Root) := do
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
    let (result, next) := sign preset config eip3076Policy state identifier document
    let signed := match result with
      | .signed _ => (blockOfCall? preset config identifier document).toList
      | _ => []
    signed ++ signedBlocks preset config next rest

/-- The votes that a run of calls signs under the rule of EIP-3076, in order. -/
def signedVotes (preset : Preset) (config : Config) :
    SignerState → List (String × Json) → List (BLSPubkey × AttestationData × Root)
  | _, [] => []
  | state, (identifier, document) :: rest =>
    let (result, next) := sign preset config eip3076Policy state identifier document
    let signed := match result with
      | .signed _ => (voteOfCall? preset config identifier document).toList
      | _ => []
    signed ++ signedVotes preset config next rest

end EthLib.Consensus.RemoteSigningApi
