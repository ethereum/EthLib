module

public import EthLib.Consensus.ConsensusVersion
public import EthLib.Consensus.Containers.BuilderApi

/-!
# `Consensus.BuilderApi.Encoding`

The versioned bodies of the Builder API, its version header, and the body of a registration.

A JSON response of the Builder API carries its data under the consensus version of that data.

The SSZ form of a body carries no version, so a header names it.

The [API description] fixes the version names and the bodies.

The [Gloas builder] document requires the header on every request with a body.

[API description]: https://github.com/ethereum/builder-specs/blob/0911550c65b1e4a326fe7fbd7d0ca52ff0b6a4b7/builder-oapi.yaml
[Gloas builder]: https://github.com/ethereum/builder-specs/blob/0911550c65b1e4a326fe7fbd7d0ca52ff0b6a4b7/specs/gloas/builder.md#per-request-validator-inputs
-/

@[expose] public section

namespace EthLib.Consensus.BuilderApi

open Base Serialization.Ssz

/-- The consensus version that the Builder API gives a fork, if it gives one.

The Builder API starts at the Merge, so it names no earlier version.

Hegotá has no consensus version yet, so it has none here either. -/
def builderVersion? (fork : Fork) : Option ConsensusVersion :=
  -- The version of the fork from Bellatrix on, and none before.
  if .bellatrix ≤ fork then fork.consensusVersion? else none

/-- The versions that the Builder API names, from Bellatrix to Gloas.

The [schema] of the API restricts the consensus versions to these.

[schema]: https://github.com/ethereum/builder-specs/blob/0911550c65b1e4a326fe7fbd7d0ca52ff0b6a4b7/builder-oapi.yaml#L79-L82
-/
def builderVersions : List ConsensusVersion :=
  [.bellatrix, .capella, .deneb, .electra, .fulu, .gloas]

/-- Whether the Builder API names a version. -/
def isBuilderVersion (version : ConsensusVersion) : Bool := version ∈ builderVersions

/-- The status that the version header of a request gives, when it decides one.

From Gloas this applies to every request with a body.

Before Gloas it applies to the SSZ body of a signed blinded block. -/
def versionHeaderStatus (header : Option String) : Option Nat :=
  match header.bind ConsensusVersion.ofName? with
  -- The exact name of a version of the Builder API decides no status, and any other gets 400.
  | some version => if isBuilderVersion version then none else some 400
  -- A header that is absent, or that names no version, gets 400.
  | none => some 400

/-- The body of a request that registers validators: a list of signed registrations.

Its JSON form is a plain array of registrations, with no version.

[`validators.yaml`] fixes its bound as the bound of the registry of validators.

[`validators.yaml`]: https://github.com/ethereum/builder-specs/blob/0911550c65b1e4a326fe7fbd7d0ca52ff0b6a4b7/apis/builder/validators.yaml
-/
abbrev RegistrationsBody (preset : Preset) : Type :=
  SszList SignedValidatorRegistrationV1 preset.VALIDATOR_REGISTRY_LIMIT.toNat

end EthLib.Consensus.BuilderApi
