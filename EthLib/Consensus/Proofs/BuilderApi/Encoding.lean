module

public import EthLib.Consensus.BuilderApi.Encoding
public import EthLib.Consensus.Proofs.ConsensusVersion

/-!
# Proofs: the versioned bodies of the Builder API

A fork has a version of the Builder API exactly from Bellatrix up to, but not including, Hegotá.

Forks with the same version give a bid and a blinded body the same top-level field names.

The Builder API names exactly the consensus versions from Bellatrix on.

The version header passes exactly when it is the exact name of a version of the Builder API.

The version of every fork from Bellatrix up to Hegotá passes.
-/

@[expose] public section

namespace EthLib.Consensus.BuilderApi

open Base

/-- A fork has a version of the Builder API exactly from Bellatrix up to, but not including, Hegotá.
-/
theorem builderVersion?_isSome_iff (fork : Fork) :
    (builderVersion? fork).isSome ↔ .bellatrix ≤ fork ∧ fork < .hegota := by
  cases fork <;> decide

/-- Every version that the Builder API gives a fork is a version of the Builder API. -/
theorem isBuilderVersion_of_builderVersion? {fork : Fork} {version : ConsensusVersion}
    (h : builderVersion? fork = some version) : isBuilderVersion version := by
  cases fork <;> cases version <;> first | decide | exact absurd h (by decide)

/-- The Builder API names a consensus version exactly when it comes at or after Bellatrix. -/
theorem isBuilderVersion_iff (version : ConsensusVersion) :
    isBuilderVersion version ↔ .bellatrix ≤ version := by
  cases version <;> decide

/-- A fork gives a bid the field names of the first fork of its version. -/
theorem BuilderBid.names_of_builderVersion? {fork : Fork} {version : ConsensusVersion}
    (h : builderVersion? fork = some version) :
    BuilderBid.names fork = BuilderBid.names version.fork := by
  cases fork <;> cases version <;> first | rfl | exact absurd h (by decide)

/-- A fork gives a blinded body the field names of the first fork of its version. -/
theorem BlindedBeaconBlockBody.names_of_builderVersion? {fork : Fork}
    {version : ConsensusVersion} (h : builderVersion? fork = some version) :
    BlindedBeaconBlockBody.names fork = BlindedBeaconBlockBody.names version.fork := by
  cases fork <;> cases version <;> first | rfl | exact absurd h (by decide)

/-- Two forks with the same version give a bid, and a blinded body, the same field names.

The names are those of the top level; nested containers are not compared. -/
theorem builderVersion?_names {fork fork' : Fork} {version : ConsensusVersion}
    (h : builderVersion? fork = some version) (h' : builderVersion? fork' = some version) :
    BuilderBid.names fork = BuilderBid.names fork' ∧
      BlindedBeaconBlockBody.names fork = BlindedBeaconBlockBody.names fork' :=
  ⟨(BuilderBid.names_of_builderVersion? h).trans (BuilderBid.names_of_builderVersion? h').symm,
    (BlindedBeaconBlockBody.names_of_builderVersion? h).trans
      (BlindedBeaconBlockBody.names_of_builderVersion? h').symm⟩

/-- The version header decides no status exactly when it names a version of the Builder API.

The name must be spelled exactly as the schema writes it. -/
theorem versionHeaderStatus_eq_none_iff (header : Option String) :
    versionHeaderStatus header = none ↔
      ∃ version, header = some version.name ∧ isBuilderVersion version := by
  unfold versionHeaderStatus
  constructor
  · intro h
    cases header with
    | none => simp at h
    | some name =>
      cases named : ConsensusVersion.ofName? name with
      | none => simp [named] at h
      | some version =>
        simp only [Option.bind_some, named] at h
        split at h
        · exact ⟨version, by rw [ConsensusVersion.name_of_ofName? named], by assumption⟩
        · simp at h
  · rintro ⟨version, rfl, builder⟩
    simp [ConsensusVersion.ofName?_name, builder]

/-- The version that the Builder API gives a fork passes the version header. -/
theorem versionHeaderStatus_builderVersion? {fork : Fork} {version : ConsensusVersion}
    (h : builderVersion? fork = some version) : versionHeaderStatus (some version.name) = none :=
  (versionHeaderStatus_eq_none_iff _).2 ⟨version, rfl, isBuilderVersion_of_builderVersion? h⟩

end EthLib.Consensus.BuilderApi
