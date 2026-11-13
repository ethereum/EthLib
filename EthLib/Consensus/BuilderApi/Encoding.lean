module

public import EthLib.Consensus.BeaconApi.Encoding
public import EthLib.Consensus.Containers.BuilderApi

/-!
# `Consensus.BuilderApi.Encoding`

The versioned bodies of the Builder API, its version header, and the body of a registration.

A JSON response of the Builder API carries its data under the consensus version of that data.

The SSZ form of a body carries no version, so a header names it.

The [API description] fixes the version names and the bodies.

The [Gloas builder] document requires the header on every request with a body.

[API description]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/builder-oapi.yaml
[Gloas builder]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/gloas/builder.md#per-request-validator-inputs
-/

@[expose] public section

namespace EthLib.Consensus.BuilderApi

open Base Serialization.Ssz BeaconApi

/-- The consensus version that the Builder API gives a fork, if it gives one.

It is the version of the fork from Bellatrix on.

The Builder API starts at the Merge, so it names no earlier version.

Hegotá has no consensus version yet, so it has none here either. -/
def builderVersion? (fork : Fork) : Option ConsensusVersion :=
  if .bellatrix ≤ fork then fork.consensusVersion? else none

/-- The versions that the Builder API names, from Bellatrix to Gloas.

The [schema] of the API restricts the consensus versions to these.

[schema]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/builder-oapi.yaml#L79-L82
-/
def builderVersions : List ConsensusVersion :=
  [.bellatrix, .capella, .deneb, .electra, .fulu, .gloas]

/-- Whether the Builder API names a version. -/
def isBuilderVersion (version : ConsensusVersion) : Bool := version ∈ builderVersions

/-- The status that the version header of a request gives, when it decides one.

A header that is absent gives 400.

So does a header that is not the exact name of a version of the Builder API.

Otherwise the header decides no status.

From Gloas this applies to every request with a body.

Before Gloas it applies to the SSZ body of a signed blinded block. -/
def versionHeaderStatus (header : Option String) : Option Nat :=
  match header.bind ConsensusVersion.ofName? with
  | some version => if isBuilderVersion version then none else some 400
  | none => some 400

/-- The body of a request that registers validators: a list of signed registrations.

Its JSON form is a plain array of registrations, with no version.

[`validators.yaml`] fixes its bound as the bound of the registry of validators.

[`validators.yaml`]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/apis/builder/validators.yaml
-/
abbrev RegistrationsBody (preset : Preset) : Type :=
  SszList SignedValidatorRegistrationV1 preset.VALIDATOR_REGISTRY_LIMIT.toNat

end EthLib.Consensus.BuilderApi
